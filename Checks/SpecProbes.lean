import Soulgem.Spec.Eta
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
  let mbc : SCtor := { name := `MB.mk, type := .sort (.succ .zero), fields := [], idx := [] }
  let mb : SType := { name := `MB, type := .sort (.succ .zero), indices := [], ctors := [mbc] }
  { b with types := b.types ++ [mb] }

example : mutualMAMB.etaCtor?.isSome = false := by decide

-- Level instantiation: Spec's `instK` simplifies `max u u` to `u` whatever the objects are
-- (rc3 keeps `max u u` when the level object is shared: Kernel.lean, `T1.rec has max`).
example : VLevel.instK [.param 0] (.max (.param 0) (.param 0)) = .param 0 := by decide

end SpecProbes
