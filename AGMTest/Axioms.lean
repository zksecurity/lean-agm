import AlgebraicGroupModel
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Every declaration in the exported namespace stays inside Lean's standard axiom footprint. -/

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[`AlgebraicGroupModel.Adversary, `AlgebraicGroupModel.MultiGroup.Adversary,
      `AlgebraicGroupModel.Output, `AlgebraicGroupModel.Transcript,
      `AlgebraicGroupModel.Interaction.erase, `AlgebraicGroupModel.Interaction.Core.run,
      `AlgebraicGroupModel.Interaction.run, `AlgebraicGroupModel.Interaction.run_pure,
      `AlgebraicGroupModel.Interaction.run_query, `AlgebraicGroupModel.Interaction.run_valid] do
    if (← getEnv).contains name then
      throwError "Removed interface or adapter has returned: {name}"
  for (name, _) in (← getEnv).constants.toList do
    if (`AlgebraicGroupModel).isPrefixOf name then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unexpected axiom in {name}: {axiomName}"
