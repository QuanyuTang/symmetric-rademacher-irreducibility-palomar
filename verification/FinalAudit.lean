module

import PalomarBernoulliSolution
import SymmetricBernoulliIrreducibility
import Lean.Util.CollectAxioms

/-! Check the transitive axioms of the final and compared statements. -/

open Lean

run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for decl in #[`Bernoulli.reducibility_bound, `PalomarBernoulli.main_result] do
    let unexpected := (← collectAxioms decl).filter (!allowed.contains ·)
    unless unexpected.isEmpty do
      throwError "{decl} uses unapproved axioms {unexpected}"
