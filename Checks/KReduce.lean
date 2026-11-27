import Lean4Lean.Theory.Typing.Lemmas
import Soulgem.Spec.WF
/-! # Syntactic typing and beta spines for concrete `IsDefEq` derivations

`infer` reads a type off a term with no conversion, so each result it returns is a typing that the
rules of `IsDefEq` give directly (`infer_sound`); the `…B` checks below read `SBlock.WF`'s typing
conditions off it. `betaSpine` applies a lambda telescope to
arguments and beta-reduces, checking each step's premises with `infer` (`betaSpine_sound`).
-/
namespace Soulgem.Checks
open Lean4Lean Soulgem.Spec

def lookupTy : List VExpr → Nat → Option VExpr
  | [], _ => none
  | A :: _, 0 => some A.lift
  | _ :: Γ, n + 1 => (lookupTy Γ n).map VExpr.lift

theorem lookupTy_sound : ∀ {Γ : List VExpr} {i : Nat} {A : VExpr}, lookupTy Γ i = some A →
    Lookup Γ i A
  | _ :: _, 0, _, h => by cases h; exact .zero
  | _ :: Γ, n + 1, A, h => by
    simp only [lookupTy, Option.map_eq_some_iff] at h
    obtain ⟨B, hB, rfl⟩ := h
    exact .succ (lookupTy_sound hB)

/-- The type of `e` in `Γ`, by the typing rules alone (no conversion). -/
def infer (env : VEnv) (U : Nat) : List VExpr → VExpr → Option VExpr
  | Γ, .bvar i => lookupTy Γ i
  | _, .sort u => if u.WF U then some (.sort (.succ u)) else none
  | _, .const c ls =>
    match env.constants c with
    | some ci => if (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars then some (ci.type.instL ls) else none
    | none => none
  | Γ, .app f a =>
    match infer env U Γ f with
    | some (.forallE A B) => if infer env U Γ a = some A then some (B.inst a) else none
    | _ => none
  | Γ, .lam A b =>
    match infer env U Γ A, infer env U (A :: Γ) b with
    | some (.sort _), some B => some (.forallE A B)
    | _, _ => none
  | Γ, .forallE A b =>
    match infer env U Γ A, infer env U (A :: Γ) b with
    | some (.sort u), some (.sort v) => some (.sort (.imax u v))
    | _, _ => none

theorem infer_sound {env : VEnv} {U : Nat} :
    ∀ {Γ : List VExpr} {e A : VExpr}, infer env U Γ e = some A → env.HasType U Γ e A
  | _, .bvar _, _, h => .bvar (lookupTy_sound h)
  | _, .sort _, _, h => by
    unfold infer at h
    split at h
    · cases h; exact VEnv.HasType.sort ‹_›
    · cases h
  | _, .const _ _, _, h => by
    unfold infer at h
    split at h
    · next ci hc =>
      split at h
      · next hw => cases h; exact VEnv.HasType.const hc hw.1 hw.2
      · cases h
    · cases h
  | _, .app _ _, _, h => by
    unfold infer at h
    split at h
    · next hf =>
      split at h
      · next ha => cases h; exact VEnv.HasType.app (infer_sound hf) (infer_sound ha)
      · cases h
    · cases h
  | _, .lam _ _, _, h => by
    unfold infer at h
    split at h
    · next hA hb => cases h; exact VEnv.HasType.lam (infer_sound hA) (infer_sound hb)
    · cases h
  | _, .forallE _ _, _, h => by
    unfold infer at h
    split at h
    · next hA hb => cases h; exact VEnv.HasType.forallE (infer_sound hA) (infer_sound hb)
    · cases h

/-- `A` is a type in `Γ`. -/
def isTypeB (env : VEnv) (U : Nat) (Γ : List VExpr) (A : VExpr) : Bool :=
  match infer env U Γ A with
  | some (.sort _) => true
  | _ => false

theorem isTypeB_sound {env : VEnv} {U : Nat} {Γ : List VExpr} {A : VExpr}
    (h : isTypeB env U Γ A = true) : env.IsType U Γ A := by
  unfold isTypeB at h
  split at h
  · next hA => exact ⟨_, infer_sound hA⟩
  · cases h

/-- `A` and `B` are the same type in `Γ`. -/
def defEqTyB (env : VEnv) (U : Nat) (Γ : List VExpr) (A B : VExpr) : Bool :=
  decide (A = B) && isTypeB env U Γ A

theorem defEqTyB_sound {env : VEnv} {U : Nat} {Γ : List VExpr} {A B : VExpr}
    (h : defEqTyB env U Γ A B = true) : DefEqTy env U Γ A B := by
  simp only [defEqTyB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨rfl, h⟩ := h
  exact isTypeB_sound h

/-- `A` is a type in `Γ` and has no annotation to strip. -/
def annB (env : VEnv) (U : Nat) (Γ : List VExpr) (A : VExpr) : Bool :=
  defEqTyB env U Γ A (consumeAnn A)

theorem annB_sound {env : VEnv} {U : Nat} {Γ : List VExpr} {A : VExpr}
    (h : annB env U Γ A = true) : AnnOK env U Γ A := defEqTyB_sound h

def hasTypeB (env : VEnv) (U : Nat) (Γ : List VExpr) (e A : VExpr) : Bool :=
  decide (infer env U Γ e = some A)

theorem hasTypeB_sound {env : VEnv} {U : Nat} {Γ : List VExpr} {e A : VExpr}
    (h : hasTypeB env U Γ e A = true) : env.HasType U Γ e A :=
  infer_sound (of_decide_eq_true h)

/-- Apply `G : T` to `xs`, beta-reducing each step; `none` when a premise fails to check. -/
def betaSpine (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → VExpr → List VExpr → Option (VExpr × VExpr)
  | G, T, [] => some (G, T)
  | .lam A b, .forallE A' B, x :: xs =>
    if A = A' ∧ infer env U (A :: Γ) b = some B ∧ infer env U Γ x = some A then
      betaSpine env U Γ (b.inst x) (B.inst x) xs
    else none
  | _, _, _ :: _ => none

theorem betaSpine_sound {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {xs : List VExpr} {F G T R T' : VExpr}, env.IsDefEq U Γ F G T →
      betaSpine env U Γ G T xs = some (R, T') → env.IsDefEq U Γ (appN F xs) R T'
  | [], _, _, _, _, _, hFG, h => by
    simp only [betaSpine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hFG
  | x :: xs, F, G, T, _, _, hFG, h => by
    cases G <;> cases T <;> simp only [betaSpine, reduceCtorEq] at h
    split at h
    · next hc =>
      obtain ⟨rfl, hb, hx⟩ := hc
      have hstep := (VEnv.IsDefEq.appDF hFG (infer_sound hx)).trans
        (.beta (infer_sound hb) (infer_sound hx))
      exact betaSpine_sound (xs := xs) (F := .app F x) hstep h
    · cases h

end Soulgem.Checks
