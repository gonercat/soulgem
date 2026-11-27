import Lean
/-! # Kernel probes

Declarations sent to the kernel with `addDecl`, each with the verdict expected of the pinned
toolchain's kernel. A verdict that differs from its expectation is an error, so `lake build Checks`
fails.
-/
open Lean

-- Kernel checks of `addDecl` run asynchronously by default, and an asynchronous kernel error does
-- not reach the `try` below; with this option the kernel verdict is the result of `addDecl`.
set_option Elab.async false

def verdictAs (yes no item nm : String) (want ok : Bool) (why : String := "") : MetaM Unit := do
  IO.println s!"{item} {nm}: {if ok then yes else no}{why}"
  unless ok == want do throwError "{item} {nm}: expected {if want then yes else no}"

def verdict (item nm : String) (want ok : Bool) (why : String := "") : MetaM Unit :=
  verdictAs "accepted" "refused" item nm want ok why

def probe (item nm : String) (want : Bool) (d : Declaration) : MetaM Unit := do
  let r ← try addDecl d; pure none catch e => pure (some (← e.toMessageData.toString))
  verdict item nm want r.isNone ((r.map fun m => s!" ({(m.splitOn "\n").head!})").getD "")

def thm (nm : Name) (lps : List Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := nm, levelParams := lps, type := ty, value := val }

/-- A theorem `nm : ty` proved by `Eq.refl` of the left side, where `ty` is `∀ xs, lhs = rhs`. -/
def probeRfl (item nm : String) (want : Bool) (lps : List Name) (ty : Expr) : MetaM Unit := do
  let val ← Meta.forallTelescope ty fun xs body => do
    let some (_, lhs, _) := body.eq? | throwError "{nm}: not an equation"
    Meta.mkLambdaFVars xs (← Meta.mkEqRefl lhs)
  probe item nm want (thm (.mkSimple (nm.splitOn " ").head!) lps ty val)

def ind (lps : List Name) (np : Nat) (ts : List (Name × Expr × List (Name × Expr))) : Declaration :=
  .inductDecl lps np (ts.map fun (n, t, cs) =>
    { name := n, type := t, ctors := cs.map fun (c, ct) => { name := c, type := ct } }) false

def defn (nm : Name) (lps : List Name) (ty val : Expr) : Declaration :=
  .defnDecl
    { name := nm, levelParams := lps, type := ty, value := val, hints := .abbrev, safety := .safe }

def pi (n : Name) (t b : Expr) : Expr := .forallE n t b .default
def lam (n : Name) (t b : Expr) : Expr := .lam n t b .default
def eqE (l : Level) (α a b : Expr) : Expr := mkApp3 (.const ``Eq [l]) α a b

inductive K2 {α : Type} (a : α) : α → Nat → Prop where
  | refl : K2 a a 0

/-- One constructor with a field: not a K target, though it eliminates into `Type`. -/
inductive KF {α : Type} (a : α) : α → Nat → Prop where
  | mk (n : Nat) : KF a a n

def k2Stmt : Prop := ∀ {α : Type} (a : α) (P : (b : α) → (n : Nat) → K2 a b n → Type)
    (h : P a 0 K2.refl)
  (e : K2 a a 0), @K2.rec α a P h a 0 e = h

def kfStmt : Prop := ∀ {α : Type} (a : α) (P : (b : α) → (n : Nat) → KF a b n → Type)
  (h : ∀ n, P a n (KF.mk n)) (n : Nat) (e : KF a a n), @KF.rec α a P h a n e = h n

#eval show MetaM Unit from do
  let u := Level.param `u
  let one := Level.succ .zero
  let nat := Expr.const ``Nat []
  -- Control: the kernel refuses a false equation proved by `Eq.refl`.
  probe "control" "true = false by Eq.refl" false (thm `boolBad []
    (eqE one (.const ``Bool []) (.const ``Bool.true []) (.const ``Bool.false []))
    (mkApp2 (.const ``Eq.refl [one]) (.const ``Bool []) (.const ``Bool.true [])))

  -- 1. Projections (`infer_proj`).
  let pbox (e : Expr) := Expr.app (.const `PBox [u]) e
  probe "proj" "PBox" true (ind [`u] 1 [(`PBox, pi `α (.sort u) (.sort u),
    [(`PBox.mk, pi `α (.sort u) (pi `v (.bvar 0) (pbox (.bvar 1))))])])
  probe "proj" "PBox_val" true (defn `PBox_val [`u] (pi `α (.sort u)
      (pi `x (pbox (.bvar 0)) (.bvar 1)))
    (lam `α (.sort u) (lam `x (pbox (.bvar 0)) (.proj `PBox 0 (.bvar 0)))))
  probe "proj" "Rec1" true (ind [] 0 [(`Rec1, .sort one,
    [(`Rec1.mk, pi `x (.const `Rec1 []) (pi `n nat (.const `Rec1 [])))])])
  probe "proj" "Rec1_proj" true (defn `Rec1_proj [] (pi `r (.const `Rec1 []) nat)
    (lam `r (.const `Rec1 []) (.proj `Rec1 1 (.bvar 0))))
  let idx0 := Expr.app (.const `IdxT []) (.const ``Nat.zero [])
  probe "proj" "IdxT" true (ind [] 0 [(`IdxT, pi `n nat (.sort one), [(`IdxT.mk, pi `m nat idx0)])])
  probe "proj" "IdxT_proj" true (defn `IdxT_proj [] (pi `x idx0 nat)
      (lam `x idx0 (.proj `IdxT 0 (.bvar 0))))
  probe "proj" "Bool_proj (control)" false (defn `Bool_proj []
      (pi `x (.const ``Bool []) (.const ``Bool []))
    (lam `x (.const ``Bool []) (.proj ``Bool 0 (.bvar 0))))
  let boxP (e : Expr) := Expr.app (.const `BoxP []) e
  probe "proj" "BoxP" true (ind [] 1 [(`BoxP, pi `α (.sort one) (.sort .zero),
    [(`BoxP.mk, pi `α (.sort one) (pi `v (.bvar 0) (boxP (.bvar 1))))])])
  probe "proj" "BoxP_proj (control)" false (defn `BoxP_proj []
      (pi `α (.sort one) (pi `x (boxP (.bvar 0)) (.bvar 1)))
    (lam `α (.sort one) (lam `x (boxP (.bvar 0)) (.proj `BoxP 0 (.bvar 0)))))

  -- 2. Structure and unit eta (`is_non_rec_structure`).
  let etaEq (l : Level) (tel : List (Name × Expr)) (S rhs : Expr) : Expr :=
    let close (b : Expr) (mk : Name → Expr → Expr → Expr) := tel.foldr
        (fun (n, t) acc => mk n t acc) b
    let fnTy := close (pi `x S (S.liftLooseBVars 0 1)) pi
    eqE l fnTy (close (lam `x S (.bvar 0)) lam) (close (lam `x S rhs) lam)
  let reflOf (l : Level) (ty : Expr) : Expr := match ty.getAppArgs with
    | #[fnTy, lhs, _] => mkApp2 (.const ``Eq.refl [l]) fnTy lhs
    | _ => ty
  let etaProbe (nm : String) (want : Bool) (l : Level) (lps : List Name) (ty : Expr) : MetaM Unit :=
    probe "eta" nm want (thm (.mkSimple (nm.splitOn " ").head!) lps ty (reflOf l ty))
  etaProbe "PBox_eta" true (.imax u.succ u) [`u] (etaEq (.imax u.succ u) [(`α, .sort u)]
      (pbox (.bvar 0))
    (mkApp2 (.const `PBox.mk [u]) (.bvar 1) (.proj `PBox 0 (.bvar 0))))
  let qTy := pi `p (.bvar 0) (.sort .zero)
  let sdep (a b : Expr) := mkApp2 (.const `SDep [u]) a b
  probe "eta" "SDep" true (ind [`u] 2 [(`SDep, pi `P (.sort .zero) (pi `Q qTy (.sort u)),
    [(`SDep.mk, pi `P (.sort .zero) (pi `Q qTy (pi `h1 (.bvar 1) (pi `h2 (.app (.bvar 1) (.bvar 0))
      (sdep (.bvar 3) (.bvar 2))))))])])
  etaProbe "SDep_eta" true u [`u] (etaEq u [(`P, .sort .zero), (`Q, qTy)] (sdep (.bvar 1) (.bvar 0))
    (mkApp4 (.const `SDep.mk [u]) (.bvar 2) (.bvar 1) (.proj `SDep 0 (.bvar 0))
        (.proj `SDep 1 (.bvar 0))))
  probe "eta" "MA MB (mutual)" true (ind [] 0 [(`MA, .sort one,
      [(`MA.mk, pi `n nat (.const `MA []))]),
    (`MB, .sort one, [(`MB.mk, pi `n nat (.const `MB []))])])
  etaProbe "MA_eta" true one [] (etaEq one [] (.const `MA [])
    (.app (.const `MA.mk []) (.proj `MA 0 (.bvar 0))))
  probe "eta" "UA UB (mutual)" true (ind [] 0 [(`UA, .sort one, [(`UA.mk, .const `UA [])]),
    (`UB, .sort one, [(`UB.mk, .const `UB [])])])
  let allEq (T : Expr) := pi `a T (pi `b T (eqE one T (.bvar 1) (.bvar 0)))
  probeRfl "eta" "UA_unit_eta" true [] (allEq (.const `UA []))
  etaProbe "Rec1_eta (control)" false one [] (etaEq one [] (.const `Rec1 [])
    (mkApp2 (.const `Rec1.mk []) (.proj `Rec1 0 (.bvar 0)) (.proj `Rec1 1 (.bvar 0))))
  probeRfl "eta" "Bool_unit_eta (control)" false [] (allEq (.const ``Bool []))

  -- 3. Nesting (`is_nested_inductive_app`).
  let nn := Expr.const `NestNonempty []
  probe "nest" "NestNonempty" true (ind [] 0 [(`NestNonempty, .sort .zero,
    [(`NestNonempty.mk, pi `h (.app (.const ``Nonempty [.zero]) nn) nn)])])
  probe "nest" "NestEqLocal (control)" false (ind [] 0 [(`NestEqLocal, .sort one,
    [(`NestEqLocal.mk, pi `x (.const `NestEqLocal []) (pi `h (eqE one (.const `NestEqLocal [])
        (.bvar 0) (.bvar 0))
      (.const `NestEqLocal [])))])])

  -- 4. Level instantiation in the nested translation (`update_max`): a shared `u` keeps `max u u`.
  let uu := Level.succ (Level.succ u)
  probe "level" "J" true (ind [`u] 1 [(`J, pi `α (.sort uu) (.sort uu),
    [(`J.mk, pi `α (.sort uu) (pi `a (.bvar 0) (pi `A (.sort (.max u u))
        (.app (.const `J [u]) (.bvar 2)))))])])
  probe "level" "T1 (shared u)" true (ind [`u] 0 [(`T1, .sort uu,
    [(`T1.mk, pi `x (.app (.const `J [u]) (.const `T1 [u])) (.const `T1 [u]))])])
  let v := Level.param (Name.mkSimple ("u" ++ ""))
  let vv := Level.succ (Level.succ v)
  probe "level" "T2 (fresh u)" true (ind [`u] 0 [(`T2, .sort vv,
    [(`T2.mk, pi `x (.app (.const `J [v]) (.const `T2 [v])) (.const `T2 [v]))])])
  let hasMax (n : Name) : MetaM Bool := do
    let some ci := (← getEnv).find? n | throwError "{n} missing"
    pure (((toString (repr ci.type)).splitOn "Level.max").length > 1)
  verdictAs "yes" "no" "level" "T1.rec has max" true (← hasMax `T1.rec)
  verdictAs "yes" "no" "level" "T2.rec has max (control)" false (← hasMax `T2.rec)

  -- 5. K-like reduction (`to_cnstr_when_K`): a Prop inductive whose one constructor has no fields.
  let some (.defnInfo k2) := (← getEnv).find? ``k2Stmt | throwError "k2Stmt"
  let some (.defnInfo kf) := (← getEnv).find? ``kfStmt | throwError "kfStmt"
  probeRfl "K" "K2_rec_refl" true [] k2.value
  probeRfl "K" "KF_rec_refl (control)" false [] kf.value
