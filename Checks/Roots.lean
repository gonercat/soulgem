import Lean.CoreM
import Lean.Util.CollectAxioms
import Soulgem.Standard
import Soulgem.Spec.Derivable
import Soulgem.NatAdmitted
/-! # The roots' axioms

Each root must exist and depend on no axiom outside `propext`, `Classical.choice` and `Quot.sound`
(so on no `sorryAx`); otherwise this module is an error and `lake build Checks` fails.
-/
open Lean

def roots : List Name :=
  [``Soulgem.Nested.Admits.model, ``Soulgem.Nested.consistency_admits,
   ``Soulgem.Nested.Core.consistency_nested, ``Soulgem.Nested.Core.sound_standard,
   ``Soulgem.Nested.Core.not_succ_zero_eq_zero, ``Soulgem.no_false_of_model,
   ``Soulgem.Core.coreM_model, ``Soulgem.Core.coreEnv_good,
   ``Soulgem.Spec.Admits,
   ``Soulgem.Spec.Derivable, ``Soulgem.Core.coreEnv, ``Lean4Lean.VEnv.IsDefEq,
   ``Soulgem.Nested.natBlock_admitted]

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

#eval show CoreM Unit from do
  for r in roots do
    unless (← getEnv).contains r do throwError "root {r} is not in the environment"
    let axs ← collectAxioms r
    IO.println s!"{r}: {axs.toList}"
    for a in axs do
      unless allowed.contains a do throwError "root {r} depends on axiom {a}"
  IO.println s!"{roots.length} roots, axioms within {allowed}"
