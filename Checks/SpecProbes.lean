import Soulgem.Spec.Env
/-! # Spec-side probes

The Spec half of two README divergence bullets (structure eta, level instantiation), as
kernel-checked facts about Spec's own functions: each example fails the build if Spec's rule
differs from what the bullet says.
The kernel half is `Checks/Kernel.lean`.
-/
open Lean4Lean Soulgem.Spec

namespace SpecProbes

/-- A `plain` field of type `t : Sort s`. -/
def field (t : VExpr) (s : VLevel) : SField := { ty := t, sort := s, cert := .plain t }

/-- A one-member, one-constructor block with no indices. -/
def struct (uvars : Nat) (params : List VExpr) (level : VLevel) (fs : List SField) : SBlock :=
  let c : SCtor := { name := `S.mk, type := .sort level, fields := fs, idx := [] }
  let t : SType := { name := `S, type := .sort level, indices := [], ctors := [c] }
  { uvars := uvars, params := params, level := level, types := [t] }

/-- `SDep.{u} (P : Prop) (Q : P → Prop) : Sort u := mk (h1 : P) (h2 : Q h1)` (Kernel.lean). -/
def sdep (level : VLevel) : SBlock :=
  struct 1 [.sort .zero, .forallE (.bvar 0) (.sort .zero)] level
    [field (.bvar 1) .zero, field (.app (.bvar 1) (.bvar 0)) .zero]

-- Structure eta: level possibly zero and a field depending on an earlier one: no eta in Spec
-- (the kernel accepts `SDep_eta`).
example : (sdep (.param 0)).etaCtor?.isSome = false := by decide
-- The same fields at a level that is never zero: eta.
example : (sdep (.succ (.param 0))).etaCtor?.isSome = true := by decide
-- Non-dependent fields at a level that may be zero: eta.
example : (struct 1 [.sort .zero, .sort .zero] (.param 0)
    [field (.bvar 1) .zero, field (.bvar 1) .zero]).etaCtor?.isSome = true := by decide
-- `PBox.{u} (α : Sort u) : Sort u := mk (v : α)` is not large-eliminating: no eta in Spec
-- (the kernel accepts `PBox_eta`).
example :
    (struct 1 [.sort (.param 0)] (.param 0) [field (.bvar 0) (.param 0)]).etaCtor?.isSome = false :=
  by decide
-- A two-member block (the kernel's `MA`/`MB`): no eta in Spec.
def mutualMAMB : SBlock :=
  let b := struct 0 [] (.succ .zero) [field (.const `Nat []) (.succ .zero)]
  let mbc : SCtor := { name := `MB.mk, type := .sort (.succ .zero),
                       fields := [field (.const `Nat []) (.succ .zero)], idx := [] }
  let mb : SType := { name := `MB, type := .sort (.succ .zero), indices := [], ctors := [mbc] }
  { b with types := b.types ++ [mb] }

example : mutualMAMB.etaCtor?.isSome = false := by decide

def hasMaxL : VLevel → Bool
  | .max .. => true
  | .succ l => hasMaxL l
  | .imax a b => hasMaxL a || hasMaxL b
  | _ => false

def hasMax : VExpr → Bool
  | .sort l => hasMaxL l
  | .const _ ls => ls.any hasMaxL
  | .app f a | .lam f a | .forallE f a => hasMax f || hasMax a
  | _ => false

/-- Kernel.lean's `J.{u} (α : Sort (u+2)) : Sort (u+2) := mk (a : α) (A : Sort (max u u))`. -/
def jBlock : SBlock :=
  let uu : VLevel := .succ (.succ (.param 0))
  let mu : VLevel := .max (.param 0) (.param 0)
  let c : SCtor :=
    { name := `J.mk
      type := .forallE (.sort uu) (.forallE (.bvar 0) (.forallE (.sort mu)
        (.app (.const `J [.param 0]) (.bvar 2))))
      fields := [field (.bvar 0) uu, field (.sort mu) (.succ mu)]
      idx := [] }
  { uvars := 1, params := [.sort uu], level := uu,
    types := [{ name := `J, type := .forallE (.sort uu) (.sort uu), indices := [], ctors := [c] }] }

/-- Kernel.lean's `T1.{u} : Sort (u+2) := mk (x : J.{u} T1)`. -/
def t1Decl : UDecl :=
  let t1 : VExpr := .const `T1 [.param 0]
  let t : UType :=
    { name := `T1
      type := .sort (.succ (.succ (.param 0)))
      ctors := [(`T1.mk, .forallE (.app (.const `J [.param 0]) t1) t1)] }
  { uvars := 1, nparams := 0, types := [t] }

/-- `elim` on `T1` made one auxiliary type and no constructor type of the result has a `max`. -/
def t1ElimNoMax : Bool :=
  match elim (indOf [.plain jBlock]) (fun _ => false) t1Decl with
  | .ok tr => tr.aux.length == 1 && !tr.types.any (·.ctors.any (hasMax ·.2))
  | .error _ => false

-- Level instantiation: `J.mk` has `max u u`, and Spec's nested translation of `T1` drops it
-- (`instLK` simplifies `max u u` to `u`); rc3 keeps it when the level object is shared
-- (Kernel.lean, `T1.rec has max`).
example : hasMax ((jBlock.types[0]!).ctors[0]!).type = true := by decide
example : t1ElimNoMax = true := by decide +kernel

end SpecProbes
