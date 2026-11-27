import Soulgem.Spec.Induct
/-! # The standard `Nat` block -/
namespace Soulgem.Nested
open Lean4Lean Spec

def natBlock : SBlock :=
    { uvars := 0,
      params := [],
      level := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
      types := [{ name := `Nat,
                  type := Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)),
                  indices := [],
                  ctors := [{ name := `Nat.zero,
                              type := Lean4Lean.VExpr.const `Nat [],
                              fields := [],
                              idx := [] },
                            { name := `Nat.succ,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.const `Nat [])
                                        (Lean4Lean.VExpr.const `Nat []),
                              fields := [{ ty := Lean4Lean.VExpr.const `Nat [],
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     0
                                                     [] }],
                              idx := [] }] }] }

end Soulgem.Nested
