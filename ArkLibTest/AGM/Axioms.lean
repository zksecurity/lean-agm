/-
Copyright (c) 2026 Kobi Gurkan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import ArkLib.AGM.Basic
import ArkLib.AGM.Interaction
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! # Axiom and API guards for the algebraic group model -/

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[`AGM.GroupValTable, `AGM.GroupOpOracle, `AGM.GroupExpOracle,
      `AGM.GroupEqOracle, `AGM.GroupEncodeOracle, `AGM.GroupDecodeOracle,
      `AGM.implGroupOpOracle, `AGM.implGroupExpOracle, `AGM.implGroupEqOracle,
      `AGM.implGroupEncodeOracle, `AGM.implGroupDecodeOracle] do
    if (← getEnv).contains name then
      throwError "Removed handle-based interface has returned: {name}"
  for (name, _) in (← getEnv).constants.toList do
    if (`AGM).isPrefixOf name then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unexpected axiom in {name}: {axiomName}"
