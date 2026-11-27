import Checks.Kernel
import Checks.KReduce
import Soulgem.NatAdmitted
import Soulgem.Model.NestedAssemble
import Lean4Lean.Theory.Meta
import Lean.Util.CollectAxioms
/-! # Spec derives the equation the kernel refuses for `KF_rec_refl`

Checks/Kernel.lean sends `@KF.rec α a P h a n e = h n` to the kernel, which refuses it: `KF.mk` has
a field, so `to_cnstr_when_K` does not apply. Here the same equation is derived in Spec's `IsDefEq`,
in an environment `Admits` admits: `e ≡ KF.mk n` by proof irrelevance, then KF's iota rule.
The `#eval` at the end checks that the block and the equation are the probe's, translated by
`Lean4Lean.Meta.ofExpr`.
-/
namespace Soulgem.Checks
open Lean Lean4Lean Soulgem Soulgem.Spec

def kfMk : SCtor where
  name := `KF.mk
  type := .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.forallE (.const `Nat [])
    (appN (.const `KF []) [.bvar 2, .bvar 1, .bvar 1, .bvar 0])))
  fields := [{ ty := .const `Nat [], sort := .succ .zero, cert := .plain (.const `Nat []) }]
  idx := [.bvar 1, .bvar 0]

def kfType : SType where
  name := `KF
  type := .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.forallE (.bvar 1)
    (.forallE (.const `Nat []) (.sort .zero))))
  indices := [.bvar 1, .const `Nat []]
  ctors := [kfMk]

/-- The probe's `KF {α : Type} (a : α) : α → Nat → Prop` with `mk (n : Nat) : KF a a n`. -/
def kfBlock : SBlock where
  uvars := 0
  params := [.sort (.succ .zero), .bvar 0]
  level := .zero
  types := [kfType]

theorem nat_add_isSome : (Nested.natBlock.add Core.coreEnv).isSome = true := by decide

def envN₀ : VEnv := (Nested.natBlock.add Core.coreEnv).get nat_add_isSome
def envN : VEnv := Nested.natBlock.addEta envN₀

theorem kf_add_isSome : (kfBlock.add envN).isSome = true := by decide

def envK₀ : VEnv := (kfBlock.add envN).get kf_add_isSome
/-- Core, then `Nat`, then `KF`. -/
def envK : VEnv := kfBlock.addEta envK₀

/-- The binders of `kfStmt`, innermost first: e, n, h, P, a, α. -/
def kfCtx : List VExpr :=
  [appN (.const `KF []) [.bvar 4, .bvar 3, .bvar 3, .bvar 0],
   .const `Nat [],
   .forallE (.const `Nat []) (.app (appN (.bvar 1) [.bvar 2, .bvar 0])
     (appN (.const `KF.mk []) [.bvar 3, .bvar 2, .bvar 0])),
   .forallE (.bvar 1) (.forallE (.const `Nat [])
     (.forallE (appN (.const `KF []) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]) (.sort (.succ .zero)))),
   .bvar 0,
   .sort (.succ .zero)]

/-- `@KF.rec α a P h a n e` -/
def kfLhs : VExpr :=
  appN (.const `KF.rec [.succ .zero])
    [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 4, .bvar 1, .bvar 0]
/-- `h n` -/
def kfRhs : VExpr := .app (.bvar 2) (.bvar 1)
/-- `P a n e` -/
def kfTy : VExpr := appN (.bvar 3) [.bvar 4, .bvar 1, .bvar 0]

/-- `KF.mk n` in `kfCtx`, and the recursor applied to everything but the major premise. -/
def kfMkN : VExpr := appN (.const `KF.mk []) [.bvar 5, .bvar 4, .bvar 1]
def kfRec6 : VExpr :=
  appN (.const `KF.rec [.succ .zero]) [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 4, .bvar 1]

theorem envK_iota : envK.defeqs (kfBlock.iota 0 0) := by
  obtain ⟨_, _, e₃, _, _, _, hE⟩ := BlockModel.add_spec (Option.eq_some_of_isSome kf_add_isSome)
  have hI := Nested.iota_mem_iotaFold kfBlock e₃ (d := 0) (q := 0) (by decide) (by decide)
  unfold envK envK₀; rw [hE]
  unfold SBlock.addEta; split
  · exact VEnv.addDefEq_le.defeqs hI
  · exact hI

theorem kf_rec_refl_isDefEq : envK.IsDefEq 0 kfCtx kfLhs kfRhs kfTy := by
  let ls : List VLevel := [.succ .zero]
  let df := kfBlock.iota 0 0
  have H0 : envK.IsDefEq 0 kfCtx (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) :=
    .extra envK_iota (by decide) (by decide)
  let xs : List VExpr := [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]
  let T' : VExpr := .app (appN (.bvar 3) [.bvar 4, .bvar 1]) kfMkN
  have hL : betaSpine envK 0 kfCtx (df.lhs.instL ls) (df.type.instL ls) xs =
      some (.app kfRec6 kfMkN, T') := by decide
  have hR : betaSpine envK 0 kfCtx (df.rhs.instL ls) (df.type.instL ls) xs = some (kfRhs, T') := by
    decide
  have H3 : envK.IsDefEq 0 kfCtx (.app kfRec6 kfMkN) kfRhs T' :=
    (betaSpine_sound (H0.trans H0.symm) hL).symm.trans (betaSpine_sound H0 hR)
  let p : VExpr := appN (.const `KF []) [.bvar 5, .bvar 4, .bvar 4, .bvar 1]
  have hp : infer envK 0 kfCtx p = some (.sort .zero) := by decide
  have he : infer envK 0 kfCtx (.bvar 0) = some p := by decide
  have hm : infer envK 0 kfCtx kfMkN = some p := by decide
  have H4 : envK.IsDefEq 0 kfCtx (.bvar 0) kfMkN p :=
    .proofIrrel (infer_sound hp) (infer_sound he) (infer_sound hm)
  have hf : infer envK 0 kfCtx kfRec6 = some (.forallE p (.app (appN (.bvar 4) [.bvar 5, .bvar 2])
      (.bvar 0))) := by decide
  have H5 : envK.IsDefEq 0 kfCtx kfLhs (.app kfRec6 kfMkN) kfTy := .appDF (infer_sound hf) H4
  have hP : infer envK 0 kfCtx (appN (.bvar 3) [.bvar 4, .bvar 1]) =
      some (.forallE p (.sort (.succ .zero))) := by decide
  have H6 : envK.IsDefEq 0 kfCtx T' kfTy (.sort (.succ .zero)) := .appDF (infer_sound hP) H4.symm
  exact H5.trans (.defeqDF H6 H3)

/-- Where the block or the equation differs from the kernel's, under `Lean4Lean.Meta.ofExpr`. -/
def kfMismatches : MetaM (List String) := do
  let same (a b : VExpr) : Bool := toExpr a == toExpr b
  let tr (ls : List Name) (e : Expr) : MetaM VExpr := Lean4Lean.Meta.ofExpr ls {} e
  let ty (n : Name) : MetaM Expr := do
    let some ci := (← getEnv).find? n | throwError "{n} missing"
    pure ci.type
  let some (.defnInfo d) := (← getEnv).find? ``kfStmt | throwError "kfStmt missing"
  let rec strip : Nat → Expr → List Expr → Option (List Expr × Expr)
    | 0, e, acc => some (acc, e)
    | n + 1, .forallE _ t b _, acc => strip n b (t :: acc)
    | _, _, _ => none
  let some (doms, body) := strip kfCtx.length d.value [] | throwError "kfStmt: too few binders"
  let some (eqTy, lhs, rhs) := body.eq? | throwError "kfStmt: not an equation"
  let items : List (String × Bool) :=
    [("type", same (← tr [] (← ty `KF)) kfType.type),
     ("mk type", same (← tr [] (← ty `KF.mk)) kfMk.type),
     ("rec type", same (← tr [`u] (← ty `KF.rec)) (kfBlock.recType 0)),
     ("binders", (← doms.mapM (tr [])).length == kfCtx.length &&
        ((← doms.mapM (tr [])).zip kfCtx).all fun (a, b) => same a b),
     ("lhs", same (← tr [] lhs) kfLhs), ("rhs", same (← tr [] rhs) kfRhs),
     ("eq type", same (← tr [] eqTy) kfTy)]
  pure (items.filter (!·.2) |>.map (·.1))

/-! ### `Admits` admits Nat, then `KF` -/

theorem kf_withTypes_isSome : (kfBlock.withTypes envN).isSome = true := by decide

theorem kfBlock_WF : kfBlock.WF envN := by
  have hj (j : Nat) (hj : j < kfBlock.ntypes) : j = 0 := by
    simp [kfBlock, SBlock.ntypes] at hj; omega
  have hc (c : SCtor) (hc : c ∈ (kfBlock.types[0]!).ctors) : c = kfMk := by
    simpa [kfBlock, kfType] using hc
  refine ⟨⟨List.cons_ne_nil _ _, by decide, ?_⟩, by decide, ?_, ?_, ?_⟩
  · intro j hj' c hc'
    obtain rfl := hj j hj'; obtain rfl := hc c hc'
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro f hf
    simp only [kfMk, List.mem_singleton] at hf; subst hf
    simp only [SBlock.FieldSyn]; decide
  · have h : ∀ i < kfBlock.nparams,
        isTypeB envN 0 (kfBlock.params.take i).reverse kfBlock.params[i]! = true ∧
        annB envN 0 (kfBlock.params.take i).reverse kfBlock.params[i]! = true := by decide
    exact fun i hi => ⟨isTypeB_sound (h i hi).1, annB_sound (h i hi).2⟩
  · intro t ht
    simp only [kfBlock, List.mem_singleton] at ht; subst ht
    let Γ (a : Nat) := (kfBlock.params ++ kfType.indices.take a).reverse
    have h : ∀ a < kfType.indices.length, isTypeB envN 0 (Γ a) kfType.indices[a]! = true ∧
        annB envN 0 (Γ a) kfType.indices[a]! = true := by decide
    exact ⟨fun a ha => ⟨isTypeB_sound (h a ha).1, annB_sound (h a ha).2⟩,
      defEqTyB_sound (by decide)⟩
  · refine ⟨_, Option.eq_some_of_isSome kf_withTypes_isSome, ?_⟩
    intro j hj' c hc'
    obtain rfl := hj j hj'; obtain rfl := hc c hc'
    let e₁ := (kfBlock.withTypes envN).get kf_withTypes_isSome
    have hp : ∀ i < kfBlock.nparams, defEqTyB e₁ 0 (kfBlock.params.take i).reverse
        (kfMk.paramTys kfBlock.nparams)[i]! kfBlock.params[i]! = true := by decide
    have hi : ∀ l < kfMk.idx.length,
        hasTypeB e₁ 0 (kfBlock.params ++ kfMk.fields.map (·.ty)).reverse kfMk.idx[l]!
          (kfBlock.idxType 0 kfMk.fields.length kfMk.idx l) = true := by decide
    let f (a : Nat) := kfMk.fields[a]!
    have hf : ∀ a < kfMk.fields.length,
        hasTypeB e₁ 0 (kfBlock.fieldCtx kfMk a) (f a).ty (.sort (f a).sort) &&
        annB e₁ 0 (kfBlock.fieldCtx kfMk a) (f a).ty && kfBlock.level.isAlwaysZero = true := by
      decide
    refine ⟨isTypeB_sound (by decide), fun i h => defEqTyB_sound (hp i h),
      fun l h => hasTypeB_sound (hi l h), fun a ha => ?_⟩
    have ha0 : a = 0 := by simpa [kfMk] using ha
    subst ha0
    simp only [Bool.and_eq_true] at hf
    obtain ⟨⟨h1, h2⟩, h3⟩ := hf 0 ha
    exact ⟨hasTypeB_sound h1, annB_sound h2, .inl h3, defEqTyB_sound (by decide)⟩

theorem kf_admitted : Admits Core.coreEnv envK [.plain Nested.natBlock, .plain kfBlock] :=
  .plain (.plain .base Nested.natBlock_WF (Option.eq_some_of_isSome nat_add_isSome)) kfBlock_WF
    (Option.eq_some_of_isSome kf_add_isSome)

/-- Spec admits an environment with the probe's `KF` in which `IsDefEq` derives
`@KF.rec α a P h a n e ≡ h n : P a n e` under the probe's binders. -/
theorem kf_rec_refl_derivable :
    ∃ env, Admits Core.coreEnv env [.plain Nested.natBlock, .plain kfBlock] ∧
      env.IsDefEq 0 kfCtx kfLhs kfRhs kfTy :=
  ⟨envK, kf_admitted, kf_rec_refl_isDefEq⟩

end Soulgem.Checks

-- The block and the equation are the probe's, and the theorem rests on the standard axioms only.
open Lean Soulgem.Checks in
#eval show MetaM Unit from do
  let bad ← kfMismatches
  IO.println s!"KF translation: {if bad.isEmpty then "equal" else s!"differs at {bad}"}"
  unless bad.isEmpty do throwError "KF block or equation differs from the kernel's: {bad}"
  let axs ← collectAxioms ``kf_rec_refl_derivable
  IO.println s!"kf_rec_refl_derivable: {axs.toList}"
  for a in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "kf_rec_refl_derivable depends on axiom {a}"
