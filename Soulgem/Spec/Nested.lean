import Soulgem.Spec.Induct

/-!
# Specification of nested inductive blocks

The kernel translates a nested block to a mutual block with auxiliary types
(`elim_nested_inductive_fn`), checks that block, and restores the nested occurrences
(`restore_nested`, rc3 inductive.cpp).
-/

namespace Soulgem.Spec
open Lean Lean4Lean

/-- An inductive type of the environment, as nested elimination reads it. -/
structure IndInfo where
  nparams : Nat
  /-- the members of its block -/
  all : List Name
  type : VExpr
  ctors : List (Name × VExpr)
  deriving Inhabited

/-- A user declaration: a block's types and constructors, before translation. -/
structure UType where
  name : Name
  type : VExpr
  ctors : List (Name × VExpr)
  deriving Inhabited

structure UDecl where
  uvars : Nat
  nparams : Nat
  types : List UType

def headArgs : VExpr → VExpr × List VExpr
  | .app f a => let (h, as) := headArgs f; (h, as ++ [a])
  | e => (e, [])

def mentions (ns : List Name) : VExpr → Bool
  | .const c _ => ns.contains c
  | .app f a => mentions ns f || mentions ns a
  | .lam A b | .forallE A b => mentions ns A || mentions ns b
  | _ => false

/-- Some free variable, seen under `d` binders, is bound at level `≥ n`. -/
def hasLocal (n d : Nat) : VExpr → (k : Nat := 0) → Bool
  | .bvar i, k => i ≥ k && d - 1 - (i - k) ≥ n
  | .app f a, k => hasLocal n d f k || hasLocal n d a k
  | .lam A b, k | .forallE A b, k => hasLocal n d A k || hasLocal n d b (k + 1)
  | _, _ => false

/-- Strip `k` Π-binders, returning their types and the body. -/
def stripPi : Nat → VExpr → Option (List VExpr × VExpr)
  | 0, e => some ([], e)
  | k + 1, .forallE A b => do let (As, r) ← stripPi k b; return (A :: As, r)
  | _, _ => none

/-- `instantiate_pi_params`: strip one Π per element of `Ds` and substitute it. -/
def instParams : VExpr → List VExpr → Option VExpr
  | e, [] => some e
  | .forallE _ b, D :: Ds => instParams (b.inst D) Ds
  | _, _ => none

structure Aux where
  /-- the nested occurrence `J Ds`, over the `n` parameters -/
  key : VExpr
  name : Name
  deriving Inhabited

structure NState where
  newTypes : Array UType
  aux : Array Aux := #[]
  nextIdx : Nat := 1

abbrev NM := StateT NState (Except String)

/-- `Name.appendIndexAfter` on names without macro scopes, written with `String.append`. -/
def appendIdx (base : Name) (i : Nat) : Name :=
  match base with
  | .str p s => .str p (s ++ "_" ++ toString i)
  | b => .str b ("_" ++ toString i)

variable (ind? : Name → Option IndInfo) (contains : Name → Bool) (lvls : List VLevel) (n : Nat)

/-- `mk_unique_name`: `base_i` for the first `i ≥ nextIdx` not in the environment. -/
def uniqueName (base : Name) : NM Name := do
  let s ← get
  let rec loop : Nat → Nat → Except String (Name × Nat)
    | 0, _ => .error "no fresh name"
    | fuel + 1, i =>
      let r := appendIdx base i
      if contains r then loop fuel (i + 1) else .ok (r, i)
  let (r, i) ← liftM (loop 10000 s.nextIdx)
  set { s with nextIdx := i + 1 }
  return r

/-- `replace_if_nested` at a node `e` under `d` binders, with parameter binders `Ps`. -/
def replaceIfNested (Ps : List VExpr) (d : Nat) (e : VExpr) : NM (Option VExpr) := do
  let (h, args) := headArgs e
  if args.isEmpty then return none
  let .const I I_lvls := h | return none
  let some info := ind? I | return none
  if info.nparams > args.length then return none
  let Ds := args.take info.nparams
  let names := (← get).newTypes.toList.map (·.name)
  unless Ds.any (mentions names) do return none
  if Ds.any (hasLocal n d) then
    throw s!"invalid nested inductive datatype '{I}', nested inductive datatypes parameters \
      cannot contain local variables."
  let rest := args.drop info.nparams
  let key := place d id n (appN h Ds)
  if let some a := (← get).aux.toList.find? (·.key == key) then
    return some (appN (.const a.name lvls) (vars d 0 n ++ rest))
  let DsN := Ds.map (place d id n)
  let mut result := none
  for J in info.all do
    let some Jinfo := ind? J | throw "unknown block member"
    let auxJ ← uniqueName contains (`_nested ++ J)
    let some Jty := instParams (Jinfo.type.instLK I_lvls) DsN | throw "ill-formed"
    let JKey := appN (.const J I_lvls) DsN
    modify fun s => { s with aux := s.aux.push { key := JKey, name := auxJ } }
    if J == I then result := some (appN (.const auxJ lvls) (vars d 0 n ++ rest))
    let ctors ← Jinfo.ctors.mapM fun (c, cty) => do
      let some body := instParams (cty.instLK I_lvls) DsN | throw "ill-formed"
      return (c.replacePrefix J auxJ, forallTel Ps body)
    let newType : UType := { name := auxJ, type := forallTel Ps Jty, ctors }
    modify fun s => { s with newTypes := s.newTypes.push newType }
  return result

/-- `replace_all_nested`: `replace`'s order; a replaced node is not entered. -/
def replaceAll (Ps : List VExpr) : VExpr → Nat → NM VExpr
  | e, d => do
    if let some r ← replaceIfNested ind? contains lvls n Ps d e then return r
    match e with
    | .app f a => return .app (← replaceAll Ps f d) (← replaceAll Ps a d)
    | .lam A b => return .lam (← replaceAll Ps A d) (← replaceAll Ps b (d + 1))
    | .forallE A b => return .forallE (← replaceAll Ps A d) (← replaceAll Ps b (d + 1))
    | e => return e

/-- Main loop of `elim_nested_inductive_fn`: process every type, the auxiliary types it adds too. -/
def elimLoop : Nat → Nat → NM Unit
  | 0, _ => throw "deep recursion: ElimNestedInductive.run.loop"
  | fuel + 1, i => do
    let s ← get
    if h : i < s.newTypes.size then
      let t := s.newTypes[i]
      let ctors ← t.ctors.mapM fun (c, cty) => do
        let some (Ps, body) := stripPi n cty |
          throw "invalid inductive datatype declaration, incorrect number of parameters"
        return (c, forallTel Ps (← replaceAll ind? contains lvls n Ps body n))
      modify fun s => { s with newTypes := s.newTypes.set! i { t with ctors } }
      elimLoop fuel (i + 1)
    else return

/-- The translated block, and the auxiliary types in the order they were added. -/
structure Translated where
  types : List UType
  aux : List Aux
  deriving Inhabited

def elim (u : UDecl) (fuel := 100000) : Except String Translated := do
  let lvls := (List.range u.uvars).map VLevel.param
  let (_, s) ← (elimLoop ind? contains lvls u.nparams fuel 0).run { newTypes := u.types.toArray }
  return { types := s.newTypes.toList, aux := s.aux.toList }

namespace Translated
variable (tr : Translated)

/-- The auxiliary type a constructor belongs to, if it is an auxiliary constructor. -/
def auxOfCtor? (c : Name) : Option Aux :=
  tr.aux.find? fun a => (tr.types.find? (·.name == a.name)).any (·.ctors.any (·.1 == c))

/-- `restore_nested`'s replacement at one node under `d` binders (`n` parameters outermost). -/
def restoreNode (auxRec : List (Name × Name)) (n d : Nat) (t : VExpr) : Option VExpr := do
  if let .const c ls := t then
    if let some (_, r) := auxRec.find? (·.1 == c) then return .const r ls
  let (h, args) := headArgs t
  let .const c _ := h | none
  if let some a := tr.aux.find? (·.name == c) then
    return appN (place n id d a.key) (args.drop n)
  let a ← tr.auxOfCtor? c
  let (I, Ds) := headArgs (place n id d a.key)
  let .const Ic Ils := I | none
  return appN (.const (c.replacePrefix a.name Ic) Ils) (Ds ++ args.drop n)

def restoreBody (auxRec : List (Name × Name)) (n : Nat) : VExpr → Nat → VExpr
  | t, d => match tr.restoreNode auxRec n d t with
    | some r => r
    | none => match t with
      | .app f a => .app (restoreBody auxRec n f d) (restoreBody auxRec n a d)
      | .lam A b => .lam (restoreBody auxRec n A d) (restoreBody auxRec n b (d + 1))
      | .forallE A b => .forallE (restoreBody auxRec n A d) (restoreBody auxRec n b (d + 1))
      | t => t

/-- `restore_nested`: keep the `n` parameter binders and restore the body under them. -/
def restore (auxRec : List (Name × Name)) (n : Nat) (e : VExpr) : VExpr :=
  let rec strip : Nat → VExpr → List VExpr × VExpr
    | 0, e => ([], e)
    | k + 1, .forallE A b | k + 1, .lam A b => let (As, r) := strip k b; (A :: As, r)
    | _, e => ([], e)
  let (As, body) := strip n e
  let body := tr.restoreBody auxRec n body n
  match e with
  | .lam .. => lamTel As body
  | _ => forallTel As body

end Translated

/-- A declared block: its certified block, the number of user members, and its translation. -/
structure RBlock where
  b : SBlock
  nuser : Nat
  tr : Translated
  deriving Inhabited

/-- The recorded block declaring the user type `J`, and `J`'s position in it. -/
def RBlock.find (rec : List RBlock) (J : Name) : Option (RBlock × Nat) :=
  rec.findSome? fun r =>
    ((List.range r.nuser).find? fun d => (r.b.types[d]!).name == J).map (r, ·)

/-- `J` as nested elimination reads it. -/
def RBlock.info (r : RBlock) (d : Nat) : IndInfo where
  nparams := r.b.nparams
  all := (List.range r.nuser).map fun d => (r.b.types[d]!).name
  type := (r.b.types[d]!).type
  ctors := (r.b.types[d]!).ctors.map fun c => (c.name, r.tr.restore [] r.b.nparams c.type)

def indOf (rec : List RBlock) (J : Name) : Option IndInfo :=
  (RBlock.find rec J).map fun (r, d) => r.info d

/-- Restoration preserves meaning on `e` (under `d` binders, the `n` outermost the parameters). -/
def restoreSafe (ns ms : List Name) (us : List VLevel) (n : Nat) : VExpr → Nat → Bool
  | .app f a, d =>
    match headArgs (.app f a) with
    | (.const c us', args) =>
      if ns.contains c then
        decide (us' = us) && decide (n ≤ args.length) && decide (args.take n = vars d 0 n) &&
          (args.drop n).all (!mentions ms ·)
      else restoreSafe ns ms us n f d && restoreSafe ns ms us n a d
    | _ => restoreSafe ns ms us n f d && restoreSafe ns ms us n a d
  | .const c us', _ => !ns.contains c || (decide (us' = us) && n == 0)
  | .lam A b, d | .forallE A b, d => restoreSafe ns ms us n A d && restoreSafe ns ms us n b (d + 1)
  | _, _ => true

/-- `restoreSafe` for a term whose `n` outer binders are the parameters, naming nothing in `ms`. -/
def restoreSafeTop (ns ms : List Name) (us : List VLevel) (n : Nat) (e : VExpr) : Bool :=
  let rec go : Nat → VExpr → Nat → Bool
    | 0, e, d => restoreSafe ns ms us n e d
    | k + 1, .forallE A b, d | k + 1, .lam A b, d => !mentions ms A && go k b (d + 1)
    | _, e, d => restoreSafe ns ms us n e d
  go n e 0

/-- A restored recursor: its final name, type, stored rules `(constructor, rhs)` and iota rules. -/
structure RecOut where
  name : Name
  type : VExpr
  rules : List (Name × VExpr)
  iota : List VDefEq

/-- The auxiliary recursors of a nested block and their final names (`T.rec_1`, ...). -/
def auxRecTable (b : SBlock) (nuser : Nat) : List (Name × Name) :=
  (List.range (b.ntypes - nuser)).map fun i =>
    (b.recName (nuser + i), appendIdx (Name.str (b.types[0]!).name "rec") (i + 1))

/-- The recursors of a nested block, given its certified translated block `b`, restored. -/
def nestedRecs (tr : Translated) (b : SBlock) (nuser : Nat) : List RecOut :=
  let tr : Translated := { tr with aux := tr.aux.map fun (a : Aux) => { a with key := b.sh a.key } }
  let auxRec := auxRecTable b nuser
  let n := b.nparams
  let R := tr.restore auxRec n
  (List.range b.ntypes).map fun d =>
    let t := b.types[d]!
    let name := if d < nuser then b.recName d else (auxRec[d - nuser]!).2
    let qs := List.range t.ctors.length
    let rules := qs.map fun q =>
      let c := (t.ctors[q]!).name
      let c' := if d < nuser then c else
        match tr.auxOfCtor? c with
        | some a => match headArgs a.key with
          | (.const Ic _, _) => c.replacePrefix a.name Ic
          | _ => c
        | none => c
      (c', R (b.ruleRhs d q))
    let iota := qs.map fun q =>
      let r := b.iota d q
      { r with lhs := R r.lhs, rhs := R r.rhs, type := R r.type }
    { name, type := R (b.recType d), rules, iota }

end Soulgem.Spec
