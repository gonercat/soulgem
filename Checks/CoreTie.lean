import Checks.KDerive
import Lean4Lean.Theory.Meta
/-! # The core environment's and `natBlock`'s constants have the kernel's types -/
open Lean Lean4Lean Soulgem

#eval show MetaM Unit from do
  let same (env : VEnv) (n k : Name) : MetaM Bool := do
    let some ci := (← getEnv).find? k | throwError "{k} missing"
    let kty ← Lean4Lean.Meta.ofExpr ci.levelParams {} ci.type
    pure <| match env.constants n with
      | some vc => vc.uvars == ci.levelParams.length && toExpr vc.type == toExpr kty
      | none => false
  let core := [``Eq, ``Eq.refl, ``Eq.rec, ``Iff, ``Iff.intro, ``Iff.rec, ``Nonempty,
    ``Nonempty.intro, ``Nonempty.rec, ``propext, ``Classical.choice, ``Quot.sound, ``Quot,
    ``Quot.mk, ``Quot.lift, ``Quot.ind]
  let rows := core.map (Core.coreEnv, ·) ++
    [``Nat, ``Nat.zero, ``Nat.succ, ``Nat.rec].map (Checks.envN, ·)
  let mut bad := []
  for (env, n) in rows do
    unless ← same env n n do bad := bad ++ [n]
  IO.println s!"core and Nat tie over {rows.length} constants: {if bad.isEmpty then "equal" else s!"differs at {bad}"}"
  unless bad.isEmpty do throwError "core or Nat constants differ from the kernel's: {bad}"
  if ← same Core.coreEnv ``Eq ``Iff then throwError "control: core Eq read as the kernel's Iff"
