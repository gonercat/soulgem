import Examples.Rose
import Examples.Corpus
import Examples.EtaProj
import Lean4Lean.Theory.Meta
import Lean.Util.CollectAxioms
/-! # Admitted constants' types and recursor rules equal the kernel's; theorems use std3 -/

inductive Corpus.T where
  | node : List Corpus.T → Corpus.T

namespace Corpus
mutual
inductive Ev {α : Type} (z : α) (s : α → α) : α → Prop where
  | zero : Ev z s z
  | succ {n : α} : Od z s n → Ev z s (s n)
inductive Od {α : Type} (z : α) (s : α → α) : α → Prop where
  | succ {n : α} : Ev z s n → Od z s (s n)
end

inductive B | mk : List (Array B) → B
end Corpus

namespace Soulgem.Examples
open Lean Lean4Lean Soulgem.Spec

/-- Items where the admitted data differ from the kernel's under `ofExpr`; the item count. -/
def exampleMismatches : MetaM (List String × Nat) := do
  let same (a b : VExpr) : Bool := toExpr a == toExpr b
  let constEq (venv : VEnv) (n : Name) : MetaM Bool := do
    let some ci := (← getEnv).find? n | throwError "{n} missing"
    let kty ← Lean4Lean.Meta.ofExpr ci.levelParams {} ci.type
    pure <| match venv.constants n with
      | some vc => vc.uvars == ci.levelParams.length && same vc.type kty
      | none => false
  let rulesEq (n : Name) (rules : List (Name × VExpr)) : MetaM Bool := do
    let some (.recInfo r) := (← getEnv).find? n | throwError "{n} missing"
    if r.rules.length != rules.length then return false
    (r.rules.zip rules).allM fun (kr, (sc, srhs)) => do
      pure (kr.ctor == sc && same (← Lean4Lean.Meta.ofExpr r.levelParams {} kr.rhs) srhs)
  let roseRes := (chainN Core.coreEnv [] roseSteps).get rose_isSome
  let roseEnv := roseRes.1
  let some rT := roseRes.2[1]? | throwError "roseRec: missing Corpus.T entry"
  let nrecs := nestedRecs rT.tr rT.b rT.nuser
  let nrecRules (n : Name) : List (Name × VExpr) :=
    (nrecs.find? (·.name == n)).map (·.rules) |>.getD []
  let blockRules (b : SBlock) (i : Nat) : List (Name × VExpr) :=
    (b.types[i]!).ctors.mapIdx fun q c => (c.name, b.ruleRhs i q)
  let corpusRes := (chainN Core.coreEnv [] corpusSteps).get corpus_isSome
  let cEnv := corpusRes.1
  let some rB := corpusRes.2[4]? | throwError "corpusRec: missing Corpus.B entry"
  let bRecs := nestedRecs rB.tr rB.b rB.nuser
  let bRules (n : Name) : List (Name × VExpr) :=
    (bRecs.find? (·.name == n)).map (·.rules) |>.getD []
  let plainItems (env : VEnv) (b : SBlock) (i : Nat) (t : Name) :
      MetaM (List (String × Bool)) := do
    let cs ← (b.types[i]!).ctors.mapM fun c => do pure (c.name.toString, ← constEq env c.name)
    pure ((t.toString, ← constEq env t) :: cs ++
      [(s!"{t}.rec", (← constEq env (t ++ `rec)) && (← rulesEq (t ++ `rec) (blockRules b i)))])
  let bConsts ← [`Corpus.B, `Corpus.B.mk].mapM fun n => do pure (n.toString, ← constEq cEnv n)
  let bRecNames := [`Corpus.B.rec, `Corpus.B.rec_1, `Corpus.B.rec_2, `Corpus.B.rec_3]
  let bRecItems ← bRecNames.mapM fun n => do
    pure (n.toString, (← constEq cEnv n) && (← rulesEq n (bRules n)))
  let corpusItems := (← plainItems cEnv List_block 0 `List) ++
    (← plainItems cEnv Acc_block 0 `Acc) ++ (← plainItems cEnv Corpus_Ev_block 0 `Corpus.Ev) ++
    (← plainItems cEnv Corpus_Ev_block 1 `Corpus.Od) ++ (← plainItems cEnv Array_block 0 `Array) ++
    bConsts ++ bRecItems
  let listRules := blockRules List_block 0
  let prodRules := blockRules Prod_block 0
  let etaEnv := sndEnv.addDefEq (Prod_block.etaRuleP prodNm prodMk)
  let items : List (String × Bool) :=
    [("Corpus.T", ← constEq roseEnv `Corpus.T),
     ("Corpus.T.node", ← constEq roseEnv `Corpus.T.node),
     ("Corpus.T.rec", (← constEq roseEnv `Corpus.T.rec) &&
        (← rulesEq `Corpus.T.rec (nrecRules `Corpus.T.rec))),
     ("Corpus.T.rec_1", (← constEq roseEnv `Corpus.T.rec_1) &&
        (← rulesEq `Corpus.T.rec_1 (nrecRules `Corpus.T.rec_1))),
     ("List", ← constEq roseEnv `List),
     ("List.nil", ← constEq roseEnv `List.nil),
     ("List.cons", ← constEq roseEnv `List.cons),
     ("List.rec", (← constEq roseEnv `List.rec) && (← rulesEq `List.rec listRules)),
     ("Prod", ← constEq etaEnv `Prod),
     ("Prod.mk", ← constEq etaEnv `Prod.mk),
     ("Prod.rec", (← constEq etaEnv `Prod.rec) && (← rulesEq `Prod.rec prodRules)),
     ("Prod.fst", ← constEq etaEnv `Prod.fst),
     ("Prod.snd", ← constEq etaEnv `Prod.snd),
     ("Prod eta names", prodNames == [`Prod.fst, `Prod.snd])] ++ corpusItems
  pure (items.filter (!·.2) |>.map (·.1), items.length)

def exampleRoots : List Name :=
  [``rose_admitted, ``rose_record, ``prod_admitted, ``prod_etaRule_isSome, ``prod_etaProj_admitted,
   ``corpus_admitted, ``corpus_record]

#eval show MetaM Unit from do
  let (bad, n) ← exampleMismatches
  IO.println s!"kernel tie over {n} items: {if bad.isEmpty then "equal" else s!"differs at {bad}"}"
  unless bad.isEmpty do throwError "admitted data differ from the kernel's: {bad}"
  for r in exampleRoots do
    let axs ← collectAxioms r
    IO.println s!"{r}: {axs.toList}"
    for a in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "{r} depends on axiom {a}"

end Soulgem.Examples
