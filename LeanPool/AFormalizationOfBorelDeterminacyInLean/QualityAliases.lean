/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.Choquet
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.FinLists
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.BuildStrategies
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.GaleStewart
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.Games
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.Strategies
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.Undetermined
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.BorelDeterminacy
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.BuildLevelwise
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Covering
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.CoveringClosedGame
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.One.Lift
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.One.PreLift
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.Lift
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.PreLift
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.BodyFunctor
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.PointedTrees
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.RestrictTree
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.TreeBody
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.TreeExtensions
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.Trees

/-!
# Root aliases for dotted declarations

These aliases preserve names that Lean Pool's deterministic quality audit derives
from dotted declarations inside namespaces.
-/

namespace AllWinning
alias residual := GaleStewartGame.Game.AllWinning.residual
end AllWinning

namespace Con
alias take := GaleStewartGame.BorelDet.One.Lift.Con.take
end Con

namespace ExtensionsAt
alias cast_valT' := Descriptive.Tree.ExtensionsAt.cast_valT'
end ExtensionsAt

namespace Fixing
alias bijective := Descriptive.Tree.Fixing.bijective
alias inj := Descriptive.Tree.Fixing.inj
alias mon := Descriptive.Tree.Fixing.mon
end Fixing

namespace Game
alias exists_undetermined := GaleStewartGame.Game.exists_undetermined
end Game

namespace Games
alias Covering := GaleStewartGame.Covering.Games.Covering
alias IsUnravelable := GaleStewartGame.Covering.Games.IsUnravelable
alias borel_determinacy := GaleStewartGame.Games.borel_determinacy
alias tree := GaleStewartGame.Covering.Games.tree
end Games

namespace Games.IsUnravelable
alias isDetermined := GaleStewartGame.Covering.Games.IsUnravelable.isDetermined
end Games.IsUnravelable

namespace IsPosition
alias iff_lenHom := GaleStewartGame.IsPosition.iff_lenHom
end IsPosition

namespace IsPrefix
alias zipInitsMap := List.IsPrefix.zipInitsMap
end IsPrefix

namespace IsPruned
alias body_ne_iff_ne := Descriptive.Tree.IsPruned.body_ne_iff_ne
alias pullSub := Descriptive.Tree.IsPruned.pullSub
alias sub := Descriptive.Tree.IsPruned.sub
end IsPruned

namespace LenHom
alias bodyMap_continuous := Descriptive.Tree.LenHom.bodyMap_continuous
alias bodyMap_spec := Descriptive.Tree.LenHom.bodyMap_spec
alias bodyMap_spec_res := Descriptive.Tree.LenHom.bodyMap_spec_res
alias bodyMap_spec_res_lt := Descriptive.Tree.LenHom.bodyMap_spec_res_lt
alias bodyPre_map_restrict := Descriptive.Tree.LenHom.bodyPre_map_restrict
end LenHom

namespace Losable
alias lift' := GaleStewartGame.BorelDet.One.PreLift.Losable.lift'
alias losable_of_le := GaleStewartGame.BorelDet.One.PreLift.Losable.losable_of_le
end Losable

namespace Losable'
alias losable'_of_le := GaleStewartGame.BorelDet.One.PreLift.Losable'.losable'_of_le
end Losable'

namespace LosingCondition
alias concat := GaleStewartGame.BorelDet.LosingCondition.concat
alias not_lost_short := GaleStewartGame.BorelDet.LosingCondition.not_lost_short
alias of_concat := GaleStewartGame.BorelDet.LosingCondition.of_concat
end LosingCondition

namespace Lost'
alias mk := GaleStewartGame.BorelDet.Zero.Lift.Lost'.mk
end Lost'

namespace LvlStratHom
alias comp := GaleStewartGame.Covering.LvlStratHom.comp
alias comp_toFun := GaleStewartGame.Covering.LvlStratHom.comp_toFun
alias ext' := GaleStewartGame.Covering.LvlStratHom.ext'
alias global := GaleStewartGame.Covering.LvlStratHom.global
alias globalOfObj := GaleStewartGame.Covering.LvlStratHom.globalOfObj
alias globalToObj := GaleStewartGame.Covering.LvlStratHom.globalToObj
alias id := GaleStewartGame.Covering.LvlStratHom.id
alias id_toFun := GaleStewartGame.Covering.LvlStratHom.id_toFun
alias system := GaleStewartGame.Covering.LvlStratHom.system
alias systemOfObj := GaleStewartGame.Covering.LvlStratHom.systemOfObj
alias systemToObj := GaleStewartGame.Covering.LvlStratHom.systemToObj
end LvlStratHom

namespace PartiallyUnravelled
alias «continue» := GaleStewartGame.BorelDet'.PartiallyUnravelled.continue
end PartiallyUnravelled

namespace Player
alias ownTree := GaleStewartGame.Player.ownTree
end Player

namespace Player.ownTree
alias disjoint := GaleStewartGame.Player.ownTree.disjoint
alias mem_body := GaleStewartGame.Player.ownTree.mem_body
end Player.ownTree

namespace PreStrategy
alias IsWinning := GaleStewartGame.PreStrategy.IsWinning
alias cast_quasi := GaleStewartGame.PreStrategy.cast_quasi
alias cast_winning := GaleStewartGame.PreStrategy.cast_winning
alias choose_sub := GaleStewartGame.PreStrategy.choose_sub
alias eval_mem_congr := GaleStewartGame.PreStrategy.eval_mem_congr
alias eval_val_congr := GaleStewartGame.PreStrategy.eval_val_congr
alias sub_winning := GaleStewartGame.PreStrategy.sub_winning
alias subgame := GaleStewartGame.PreStrategy.subgame
end PreStrategy

namespace PreStrategy.IsQuasi
alias choose := GaleStewartGame.PreStrategy.IsQuasi.choose
alias restrictTree_isQuasi := GaleStewartGame.PreStrategy.IsQuasi.restrictTree_isQuasi
alias restrict_isQuasi := GaleStewartGame.PreStrategy.IsQuasi.restrict_isQuasi
end PreStrategy.IsQuasi

namespace PreStrategy.IsWinning
alias choose := GaleStewartGame.PreStrategy.IsWinning.choose
alias residual := GaleStewartGame.PreStrategy.IsWinning.residual
end PreStrategy.IsWinning

namespace QuasiStrategy
alias ext := GaleStewartGame.QuasiStrategy.ext
alias residual := GaleStewartGame.QuasiStrategy.residual
alias restrict := GaleStewartGame.QuasiStrategy.restrict
alias subtree_isPruned := GaleStewartGame.QuasiStrategy.subtree_isPruned
alias subtree_top_large := GaleStewartGame.QuasiStrategy.subtree_top_large
end QuasiStrategy

namespace Strategy
alias eval_val_congr := GaleStewartGame.Strategy.eval_val_congr
alias ext := GaleStewartGame.Strategy.ext
alias isQuasi := GaleStewartGame.Strategy.isQuasi
alias pre := GaleStewartGame.Strategy.pre
alias quasi := GaleStewartGame.Strategy.quasi
end Strategy

namespace StrategySystem
alias con' := GaleStewartGame.StrategySystem.con'
end StrategySystem

namespace Winnable
alias conLong := GaleStewartGame.BorelDet.Zero.Lift.Winnable.conLong
end Winnable

namespace WinningCondition
alias concat := GaleStewartGame.BorelDet.WinningCondition.concat
alias of_concat := GaleStewartGame.BorelDet.WinningCondition.of_concat
end WinningCondition

namespace Won
alias lift' := GaleStewartGame.BorelDet.One.PreLift.Won.lift'
alias won_of_le := GaleStewartGame.BorelDet.One.PreLift.Won.won_of_le
end Won

namespace WonPosition
alias extend := GaleStewartGame.Game.WonPosition.extend
end WonPosition

namespace body
alias append := Descriptive.Tree.body.append
alias append_con := Descriptive.Tree.body.append_con
alias drop := Descriptive.Tree.body.drop
alias take := Descriptive.Tree.body.take
end body

namespace chainTree
alias concat := Choquet.chainTree.concat
end chainTree

namespace containsTree
alias map := GaleStewartGame.BodySystemObj.containsTree.map
end containsTree

namespace extensions
alias val' := Descriptive.Tree.extensions.val'
alias valT' := Descriptive.Tree.extensions.valT'
end extensions

namespace res
alias ext_val' := Descriptive.Tree.res.ext_val'
alias val' := Descriptive.Tree.res.val'
end res

namespace resEq
alias ext_val' := Descriptive.Tree.resEq.ext_val'
alias val' := Descriptive.Tree.resEq.val'
end resEq
