import Soulgem.Spec.WF

/-! Certified blocks of kernel declarations, generated; Check.lean ties them to the kernel. -/

namespace Soulgem.Examples
open Lean4Lean Soulgem.Spec

def List_block : SBlock :=
    { uvars := 1,
      params := [Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0))],
      level := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0),
      types := [{ name := `List,
                  type := Lean4Lean.VExpr.forallE
                            (Lean4Lean.VExpr.sort
                              (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0)))
                            (Lean4Lean.VExpr.sort
                              (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0))),
                  indices := [],
                  ctors := [{ name := `List.nil,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.sort
                                          (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0)))
                                        (Lean4Lean.VExpr.app
                                          (Lean4Lean.VExpr.const `List [Lean4Lean.VLevel.param 0])
                                          (Lean4Lean.VExpr.bvar 0)),
                              fields := [],
                              idx := [] },
                            { name := `List.cons,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.sort
                                          (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0)))
                                        (Lean4Lean.VExpr.forallE
                                          (Lean4Lean.VExpr.bvar 0)
                                          (Lean4Lean.VExpr.forallE
                                            (Lean4Lean.VExpr.app
                                              (Lean4Lean.VExpr.const
                                                `List
                                                [Lean4Lean.VLevel.param 0])
                                              (Lean4Lean.VExpr.bvar 1))
                                            (Lean4Lean.VExpr.app
                                              (Lean4Lean.VExpr.const
                                                `List
                                                [Lean4Lean.VLevel.param 0])
                                              (Lean4Lean.VExpr.bvar 2)))),
                              fields := [{ ty := Lean4Lean.VExpr.bvar 0,
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0),
                                           cert := Soulgem.Spec.FieldCert.plain
                                                     (Lean4Lean.VExpr.bvar 0) },
                                         { ty := Lean4Lean.VExpr.app
                                                   (Lean4Lean.VExpr.const
                                                     `List
                                                     [Lean4Lean.VLevel.param 0])
                                                   (Lean4Lean.VExpr.bvar 1),
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0),
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     0
                                                     [] }],
                              idx := [] }] }] }

def Prod_block : SBlock :=
    { uvars := 2,
      params := [Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0)),
                 Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 1))],
      level := Lean4Lean.VLevel.max
                 (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0))
                 (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 1)),
      types := [{ name := `Prod,
                  type := Lean4Lean.VExpr.forallE
                            (Lean4Lean.VExpr.sort
                              (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0)))
                            (Lean4Lean.VExpr.forallE
                              (Lean4Lean.VExpr.sort
                                (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 1)))
                              (Lean4Lean.VExpr.sort
                                (Lean4Lean.VLevel.max
                                  (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0))
                                  (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 1))))),
                  indices := [],
                  ctors := [{ name := `Prod.mk,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.sort
                                          (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0)))
                                        (Lean4Lean.VExpr.forallE
                                          (Lean4Lean.VExpr.sort
                                            (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 1)))
                                          (Lean4Lean.VExpr.forallE
                                            (Lean4Lean.VExpr.bvar 1)
                                            (Lean4Lean.VExpr.forallE
                                              (Lean4Lean.VExpr.bvar 1)
                                              (Lean4Lean.VExpr.app
                                                (Lean4Lean.VExpr.app
                                                  (Lean4Lean.VExpr.const
                                                    `Prod
                                                    [Lean4Lean.VLevel.param 0,
                                                     Lean4Lean.VLevel.param 1])
                                                  (Lean4Lean.VExpr.bvar 3))
                                                (Lean4Lean.VExpr.bvar 2))))),
                              fields := [{ ty := Lean4Lean.VExpr.bvar 1,
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0),
                                           cert := Soulgem.Spec.FieldCert.plain
                                                     (Lean4Lean.VExpr.bvar 1) },
                                         { ty := Lean4Lean.VExpr.bvar 1,
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 1),
                                           cert := Soulgem.Spec.FieldCert.plain
                                                     (Lean4Lean.VExpr.bvar 1) }],
                              idx := [] }] }] }

def Acc_block : SBlock :=
    { uvars := 1,
      params := [Lean4Lean.VExpr.sort (Lean4Lean.VLevel.param 0),
                 Lean4Lean.VExpr.forallE
                   (Lean4Lean.VExpr.bvar 0)
                   (Lean4Lean.VExpr.forallE
                     (Lean4Lean.VExpr.bvar 1)
                     (Lean4Lean.VExpr.sort (Lean4Lean.VLevel.zero)))],
      level := Lean4Lean.VLevel.zero,
      types := [{ name := `Acc,
                  type := Lean4Lean.VExpr.forallE
                            (Lean4Lean.VExpr.sort (Lean4Lean.VLevel.param 0))
                            (Lean4Lean.VExpr.forallE
                              (Lean4Lean.VExpr.forallE
                                (Lean4Lean.VExpr.bvar 0)
                                (Lean4Lean.VExpr.forallE
                                  (Lean4Lean.VExpr.bvar 1)
                                  (Lean4Lean.VExpr.sort (Lean4Lean.VLevel.zero))))
                              (Lean4Lean.VExpr.forallE
                                (Lean4Lean.VExpr.bvar 1)
                                (Lean4Lean.VExpr.sort (Lean4Lean.VLevel.zero)))),
                  indices := [Lean4Lean.VExpr.bvar 1],
                  ctors := [{ name := `Acc.intro,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.sort (Lean4Lean.VLevel.param 0))
                                        (Lean4Lean.VExpr.forallE
                                          (Lean4Lean.VExpr.forallE
                                            (Lean4Lean.VExpr.bvar 0)
                                            (Lean4Lean.VExpr.forallE
                                              (Lean4Lean.VExpr.bvar 1)
                                              (Lean4Lean.VExpr.sort (Lean4Lean.VLevel.zero))))
                                          (Lean4Lean.VExpr.forallE
                                            (Lean4Lean.VExpr.bvar 1)
                                            (Lean4Lean.VExpr.forallE
                                              (Lean4Lean.VExpr.forallE
                                                (Lean4Lean.VExpr.bvar 2)
                                                (Lean4Lean.VExpr.forallE
                                                  (Lean4Lean.VExpr.app
                                                    (Lean4Lean.VExpr.app
                                                      (Lean4Lean.VExpr.bvar 2)
                                                      (Lean4Lean.VExpr.bvar 0))
                                                    (Lean4Lean.VExpr.bvar 1))
                                                  (Lean4Lean.VExpr.app
                                                    (Lean4Lean.VExpr.app
                                                      (Lean4Lean.VExpr.app
                                                        (Lean4Lean.VExpr.const
                                                          `Acc
                                                          [Lean4Lean.VLevel.param 0])
                                                        (Lean4Lean.VExpr.bvar 4))
                                                      (Lean4Lean.VExpr.bvar 3))
                                                    (Lean4Lean.VExpr.bvar 1))))
                                              (Lean4Lean.VExpr.app
                                                (Lean4Lean.VExpr.app
                                                  (Lean4Lean.VExpr.app
                                                    (Lean4Lean.VExpr.const
                                                      `Acc
                                                      [Lean4Lean.VLevel.param 0])
                                                    (Lean4Lean.VExpr.bvar 3))
                                                  (Lean4Lean.VExpr.bvar 2))
                                                (Lean4Lean.VExpr.bvar 1))))),
                              fields := [{ ty := Lean4Lean.VExpr.bvar 1,
                                           sort := Lean4Lean.VLevel.param 0,
                                           cert := Soulgem.Spec.FieldCert.plain
                                                     (Lean4Lean.VExpr.bvar 1) },
                                         { ty := Lean4Lean.VExpr.forallE
                                                   (Lean4Lean.VExpr.bvar 2)
                                                   (Lean4Lean.VExpr.forallE
                                                     (Lean4Lean.VExpr.app
                                                       (Lean4Lean.VExpr.app
                                                         (Lean4Lean.VExpr.bvar 2)
                                                         (Lean4Lean.VExpr.bvar 0))
                                                       (Lean4Lean.VExpr.bvar 1))
                                                     (Lean4Lean.VExpr.app
                                                       (Lean4Lean.VExpr.app
                                                         (Lean4Lean.VExpr.app
                                                           (Lean4Lean.VExpr.const
                                                             `Acc
                                                             [Lean4Lean.VLevel.param 0])
                                                           (Lean4Lean.VExpr.bvar 4))
                                                         (Lean4Lean.VExpr.bvar 3))
                                                       (Lean4Lean.VExpr.bvar 1))),
                                           sort := Lean4Lean.VLevel.zero,
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     [Lean4Lean.VExpr.bvar 2,
                                                      Lean4Lean.VExpr.app
                                                        (Lean4Lean.VExpr.app
                                                          (Lean4Lean.VExpr.bvar 2)
                                                          (Lean4Lean.VExpr.bvar 0))
                                                        (Lean4Lean.VExpr.bvar 1)]
                                                     0
                                                     [Lean4Lean.VExpr.bvar 1] }],
                              idx := [Lean4Lean.VExpr.bvar 1] }] }] }

def Corpus_Ev_block : SBlock :=
    { uvars := 0,
      params := [Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)),
                 Lean4Lean.VExpr.bvar 0,
                 Lean4Lean.VExpr.forallE (Lean4Lean.VExpr.bvar 1) (Lean4Lean.VExpr.bvar 2)],
      level := Lean4Lean.VLevel.zero,
      types := [{ name := `Corpus.Ev,
                  type := Lean4Lean.VExpr.forallE
                            (Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)))
                            (Lean4Lean.VExpr.forallE
                              (Lean4Lean.VExpr.bvar 0)
                              (Lean4Lean.VExpr.forallE
                                (Lean4Lean.VExpr.forallE
                                  (Lean4Lean.VExpr.bvar 1)
                                  (Lean4Lean.VExpr.bvar 2))
                                (Lean4Lean.VExpr.forallE
                                  (Lean4Lean.VExpr.bvar 2)
                                  (Lean4Lean.VExpr.sort (Lean4Lean.VLevel.zero))))),
                  indices := [Lean4Lean.VExpr.bvar 2],
                  ctors := [{ name := `Corpus.Ev.zero,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.sort
                                          (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)))
                                        (Lean4Lean.VExpr.forallE
                                          (Lean4Lean.VExpr.bvar 0)
                                          (Lean4Lean.VExpr.forallE
                                            (Lean4Lean.VExpr.forallE
                                              (Lean4Lean.VExpr.bvar 1)
                                              (Lean4Lean.VExpr.bvar 2))
                                            (Lean4Lean.VExpr.app
                                              (Lean4Lean.VExpr.app
                                                (Lean4Lean.VExpr.app
                                                  (Lean4Lean.VExpr.app
                                                    (Lean4Lean.VExpr.const `Corpus.Ev [])
                                                    (Lean4Lean.VExpr.bvar 2))
                                                  (Lean4Lean.VExpr.bvar 1))
                                                (Lean4Lean.VExpr.bvar 0))
                                              (Lean4Lean.VExpr.bvar 1)))),
                              fields := [],
                              idx := [Lean4Lean.VExpr.bvar 1] },
                            { name := `Corpus.Ev.succ,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.sort
                                          (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)))
                                        (Lean4Lean.VExpr.forallE
                                          (Lean4Lean.VExpr.bvar 0)
                                          (Lean4Lean.VExpr.forallE
                                            (Lean4Lean.VExpr.forallE
                                              (Lean4Lean.VExpr.bvar 1)
                                              (Lean4Lean.VExpr.bvar 2))
                                            (Lean4Lean.VExpr.forallE
                                              (Lean4Lean.VExpr.bvar 2)
                                              (Lean4Lean.VExpr.forallE
                                                (Lean4Lean.VExpr.app
                                                  (Lean4Lean.VExpr.app
                                                    (Lean4Lean.VExpr.app
                                                      (Lean4Lean.VExpr.app
                                                        (Lean4Lean.VExpr.const `Corpus.Od [])
                                                        (Lean4Lean.VExpr.bvar 3))
                                                      (Lean4Lean.VExpr.bvar 2))
                                                    (Lean4Lean.VExpr.bvar 1))
                                                  (Lean4Lean.VExpr.bvar 0))
                                                (Lean4Lean.VExpr.app
                                                  (Lean4Lean.VExpr.app
                                                    (Lean4Lean.VExpr.app
                                                      (Lean4Lean.VExpr.app
                                                        (Lean4Lean.VExpr.const `Corpus.Ev [])
                                                        (Lean4Lean.VExpr.bvar 4))
                                                      (Lean4Lean.VExpr.bvar 3))
                                                    (Lean4Lean.VExpr.bvar 2))
                                                  (Lean4Lean.VExpr.app
                                                    (Lean4Lean.VExpr.bvar 2)
                                                    (Lean4Lean.VExpr.bvar 1))))))),
                              fields := [{ ty := Lean4Lean.VExpr.bvar 2,
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.plain
                                                     (Lean4Lean.VExpr.bvar 2) },
                                         { ty := Lean4Lean.VExpr.app
                                                   (Lean4Lean.VExpr.app
                                                     (Lean4Lean.VExpr.app
                                                       (Lean4Lean.VExpr.app
                                                         (Lean4Lean.VExpr.const `Corpus.Od [])
                                                         (Lean4Lean.VExpr.bvar 3))
                                                       (Lean4Lean.VExpr.bvar 2))
                                                     (Lean4Lean.VExpr.bvar 1))
                                                   (Lean4Lean.VExpr.bvar 0),
                                           sort := Lean4Lean.VLevel.zero,
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     1
                                                     [Lean4Lean.VExpr.bvar 0] }],
                              idx := [Lean4Lean.VExpr.app
                                        (Lean4Lean.VExpr.bvar 2)
                                        (Lean4Lean.VExpr.bvar 1)] }] },
                { name := `Corpus.Od,
                  type := Lean4Lean.VExpr.forallE
                            (Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)))
                            (Lean4Lean.VExpr.forallE
                              (Lean4Lean.VExpr.bvar 0)
                              (Lean4Lean.VExpr.forallE
                                (Lean4Lean.VExpr.forallE
                                  (Lean4Lean.VExpr.bvar 1)
                                  (Lean4Lean.VExpr.bvar 2))
                                (Lean4Lean.VExpr.forallE
                                  (Lean4Lean.VExpr.bvar 2)
                                  (Lean4Lean.VExpr.sort (Lean4Lean.VLevel.zero))))),
                  indices := [Lean4Lean.VExpr.bvar 2],
                  ctors := [{ name := `Corpus.Od.succ,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.sort
                                          (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero)))
                                        (Lean4Lean.VExpr.forallE
                                          (Lean4Lean.VExpr.bvar 0)
                                          (Lean4Lean.VExpr.forallE
                                            (Lean4Lean.VExpr.forallE
                                              (Lean4Lean.VExpr.bvar 1)
                                              (Lean4Lean.VExpr.bvar 2))
                                            (Lean4Lean.VExpr.forallE
                                              (Lean4Lean.VExpr.bvar 2)
                                              (Lean4Lean.VExpr.forallE
                                                (Lean4Lean.VExpr.app
                                                  (Lean4Lean.VExpr.app
                                                    (Lean4Lean.VExpr.app
                                                      (Lean4Lean.VExpr.app
                                                        (Lean4Lean.VExpr.const `Corpus.Ev [])
                                                        (Lean4Lean.VExpr.bvar 3))
                                                      (Lean4Lean.VExpr.bvar 2))
                                                    (Lean4Lean.VExpr.bvar 1))
                                                  (Lean4Lean.VExpr.bvar 0))
                                                (Lean4Lean.VExpr.app
                                                  (Lean4Lean.VExpr.app
                                                    (Lean4Lean.VExpr.app
                                                      (Lean4Lean.VExpr.app
                                                        (Lean4Lean.VExpr.const `Corpus.Od [])
                                                        (Lean4Lean.VExpr.bvar 4))
                                                      (Lean4Lean.VExpr.bvar 3))
                                                    (Lean4Lean.VExpr.bvar 2))
                                                  (Lean4Lean.VExpr.app
                                                    (Lean4Lean.VExpr.bvar 2)
                                                    (Lean4Lean.VExpr.bvar 1))))))),
                              fields := [{ ty := Lean4Lean.VExpr.bvar 2,
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.zero),
                                           cert := Soulgem.Spec.FieldCert.plain
                                                     (Lean4Lean.VExpr.bvar 2) },
                                         { ty := Lean4Lean.VExpr.app
                                                   (Lean4Lean.VExpr.app
                                                     (Lean4Lean.VExpr.app
                                                       (Lean4Lean.VExpr.app
                                                         (Lean4Lean.VExpr.const `Corpus.Ev [])
                                                         (Lean4Lean.VExpr.bvar 3))
                                                       (Lean4Lean.VExpr.bvar 2))
                                                     (Lean4Lean.VExpr.bvar 1))
                                                   (Lean4Lean.VExpr.bvar 0),
                                           sort := Lean4Lean.VLevel.zero,
                                           cert := Soulgem.Spec.FieldCert.recursive
                                                     []
                                                     0
                                                     [Lean4Lean.VExpr.bvar 0] }],
                              idx := [Lean4Lean.VExpr.app
                                        (Lean4Lean.VExpr.bvar 2)
                                        (Lean4Lean.VExpr.bvar 1)] }] }] }

def Array_block : SBlock :=
    { uvars := 1,
      params := [Lean4Lean.VExpr.sort (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0))],
      level := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0),
      types := [{ name := `Array,
                  type := Lean4Lean.VExpr.forallE
                            (Lean4Lean.VExpr.sort
                              (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0)))
                            (Lean4Lean.VExpr.sort
                              (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0))),
                  indices := [],
                  ctors := [{ name := `Array.mk,
                              type := Lean4Lean.VExpr.forallE
                                        (Lean4Lean.VExpr.sort
                                          (Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0)))
                                        (Lean4Lean.VExpr.forallE
                                          (Lean4Lean.VExpr.app
                                            (Lean4Lean.VExpr.const `List [Lean4Lean.VLevel.param 0])
                                            (Lean4Lean.VExpr.bvar 0))
                                          (Lean4Lean.VExpr.app
                                            (Lean4Lean.VExpr.const
                                              `Array
                                              [Lean4Lean.VLevel.param 0])
                                            (Lean4Lean.VExpr.bvar 1))),
                              fields := [{ ty := Lean4Lean.VExpr.app
                                                   (Lean4Lean.VExpr.const
                                                     `List
                                                     [Lean4Lean.VLevel.param 0])
                                                   (Lean4Lean.VExpr.bvar 0),
                                           sort := Lean4Lean.VLevel.succ (Lean4Lean.VLevel.param 0),
                                           cert := Soulgem.Spec.FieldCert.plain
                                                     (Lean4Lean.VExpr.app
                                                       (Lean4Lean.VExpr.const
                                                         `List
                                                         [Lean4Lean.VLevel.param 0])
                                                       (Lean4Lean.VExpr.bvar 0)) }],
                              idx := [] }] }] }

end Soulgem.Examples
