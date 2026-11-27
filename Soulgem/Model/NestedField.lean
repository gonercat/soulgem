import Soulgem.Model.NestedData

/-! # Nested blocks: auxiliary constructors field by field -/

namespace Soulgem.Nested
open Lean4Lean Spec

/-! ## Restoration on telescopes -/

section Restore
variable (tr : Translated) (auxRec : List (Name × Name)) (n : Nat)

theorem restore_strip : ∀ (As : List VExpr) (X : VExpr),
    Translated.restore.strip As.length (Spec.forallTel As X) = (As, X)
  | [], _ => by simp [Translated.restore.strip, Spec.forallTel]
  | A :: As, X => by simp [Spec.forallTel, Translated.restore.strip, restore_strip As X]

theorem restore_forallTel (As : List VExpr) (X : VExpr) (h : As.length = n) :
    tr.restore auxRec n (Spec.forallTel As X) = Spec.forallTel As
        (tr.restoreBody auxRec n X n) := by
  subst h
  unfold Translated.restore
  rw [restore_strip]
  cases As with
  | nil => simp only [Spec.forallTel]; split <;> rfl
  | cons A As => simp only [Spec.forallTel]

end Restore

/-! ## The field correspondence -/

theorem getElem!_map' {α β : Type _} [Inhabited α] [Inhabited β] (f : α → β) {l : List α} {k : Nat}
    (h : k < l.length) : (l.map f)[k]! = f l[k]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

section Corr
open ConLeche ConLeche.SetTheory BlockModel
universe u
variable {V : Type u} [SetTheory V] {M : CInterp V} {env env₁ : VEnv} {b : SBlock}
  {MJ : CInterp V} {envJ envJ₁ : VEnv} {rec : List RBlock} {n : Nat} {tr : Translated}
  {nuser : Nat} {fams : List Fam}
  {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr} {r : RBlock} {m d : Nat}

def AllSpec (rec : List RBlock) (n : Nat) (tr : Translated) (b : SBlock) (nuser : Nat)
    (fams : List Fam) : Prop :=
  ∀ a ∈ tr.aux, ∃ J lv Ds r m d, Slot rec n tr b nuser fams a J lv Ds r m d

theorem headArgs_appN_const (c : Name) (us : List VLevel) (as : List VExpr) :
    headArgs (appN (.const c us) as) = (.const c us, as) := by
  rw [headArgs_appN]; simp [headArgs]

end Corr

end Soulgem.Nested
