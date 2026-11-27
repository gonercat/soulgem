import Soulgem.Spec.WF

/-! Nested declarations and their translations' certified blocks, generated. -/

namespace Soulgem.Examples
open Lean4Lean Soulgem.Spec

def Corpus_T_udecl : UDecl :=
    { uvars := 0,
      nparams := 0,
      types := [{ name := `Corpus.T,
                  type := Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)),
                  ctors := [(`Corpus.T.node,
                             Lean4Lean.VExpr.forallE
                               (Lean4Lean.VExpr.app
                                 (Lean4Lean.VExpr.const `List [Lean4Lean.VLevel.zero])
                                 (Lean4Lean.VExpr.const `Corpus.T []))
                               (Lean4Lean.VExpr.const `Corpus.T []))] }] }

def Corpus_T_tblock : SBlock :=
    { uvars := 0,
      params := [],
      level := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
      types := [{ name := `Corpus.T,
                  type := Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)),
                  indices := [],
                  ctors := [{ name := `Corpus.T.node,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.const `_nested.List_1 [])
                                        (Lean4Lean.VExpr.const `Corpus.T []),
                              fields := [{ ty := Lean4Lean.VExpr.const `_nested.List_1 [],
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     1
                                                     [] }],
                              idx := [] }] },
                { name := `_nested.List_1,
                  type := Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)),
                  indices := [],
                  ctors := [{ name := `_nested.List_1.nil,
                              type := Lean4Lean.VExpr.const `_nested.List_1 [],
                              fields := [],
                              idx := [] },
                            { name := `_nested.List_1.cons,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.const `Corpus.T [])
                                        (Lean4Lean.VExpr.forallE
                                          (Lean4Lean.VExpr.const `_nested.List_1 [])
                                          (Lean4Lean.VExpr.const `_nested.List_1 [])),
                              fields := [{ ty := Lean4Lean.VExpr.const `Corpus.T [],
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     0
                                                     [] },
                                         { ty := Lean4Lean.VExpr.const `_nested.List_1 [],
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     1
                                                     [] }],
                              idx := [] }] }] }

def Corpus_B_udecl : UDecl :=
    { uvars := 0,
      nparams := 0,
      types := [{ name := `Corpus.B,
                  type := Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)),
                  ctors := [(`Corpus.B.mk,
                             Lean4Lean.VExpr.forallE
                               (Lean4Lean.VExpr.app
                                 (Lean4Lean.VExpr.const `List [Lean4Lean.VLevel.zero])
                                 (Lean4Lean.VExpr.app
                                   (Lean4Lean.VExpr.const `Array [Lean4Lean.VLevel.zero])
                                   (Lean4Lean.VExpr.const `Corpus.B [])))
                               (Lean4Lean.VExpr.const `Corpus.B []))] }] }

def Corpus_B_tblock : SBlock :=
    { uvars := 0,
      params := [],
      level := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
      types := [{ name := `Corpus.B,
                  type := Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)),
                  indices := [],
                  ctors := [{ name := `Corpus.B.mk,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.const `_nested.List_1 [])
                                        (Lean4Lean.VExpr.const `Corpus.B []),
                              fields := [{ ty := Lean4Lean.VExpr.const `_nested.List_1 [],
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     1
                                                     [] }],
                              idx := [] }] },
                { name := `_nested.List_1,
                  type := Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)),
                  indices := [],
                  ctors := [{ name := `_nested.List_1.nil,
                              type := Lean4Lean.VExpr.const `_nested.List_1 [],
                              fields := [],
                              idx := [] },
                            { name := `_nested.List_1.cons,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.const `_nested.Array_2 [])
                                        (Lean4Lean.VExpr.forallE
                                          (Lean4Lean.VExpr.const `_nested.List_1 [])
                                          (Lean4Lean.VExpr.const `_nested.List_1 [])),
                              fields := [{ ty := Lean4Lean.VExpr.const `_nested.Array_2 [],
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     2
                                                     [] },
                                         { ty := Lean4Lean.VExpr.const `_nested.List_1 [],
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     1
                                                     [] }],
                              idx := [] }] },
                { name := `_nested.Array_2,
                  type := Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)),
                  indices := [],
                  ctors := [{ name := `_nested.Array_2.mk,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.const `_nested.List_3 [])
                                        (Lean4Lean.VExpr.const `_nested.Array_2 []),
                              fields := [{ ty := Lean4Lean.VExpr.const `_nested.List_3 [],
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     3
                                                     [] }],
                              idx := [] }] },
                { name := `_nested.List_3,
                  type := Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)),
                  indices := [],
                  ctors := [{ name := `_nested.List_3.nil,
                              type := Lean4Lean.VExpr.const `_nested.List_3 [],
                              fields := [],
                              idx := [] },
                            { name := `_nested.List_3.cons,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.const `Corpus.B [])
                                        (Lean4Lean.VExpr.forallE
                                          (Lean4Lean.VExpr.const `_nested.List_3 [])
                                          (Lean4Lean.VExpr.const `_nested.List_3 [])),
                              fields := [{ ty := Lean4Lean.VExpr.const `Corpus.B [],
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     0
                                                     [] },
                                         { ty := Lean4Lean.VExpr.const `_nested.List_3 [],
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     3
                                                     [] }],
                              idx := [] }] }] }

end Soulgem.Examples
