import Soulgem.Model.NestedScope

/-! # Restoring with different keys -/

namespace Soulgem
open ConLeche ConLeche.SetTheory Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V]

def KeyAgree (M' : CInterp V) (ls : List Nat) (n : Nat) (Q : List V → Prop) (k₁ k₂ : VExpr) :
    Prop :=
  k₂.ClosedN n ∧ ∃ Ic Ils₁ Ils₂ Ds₁ Ds₂, headArgs k₁ = (.const Ic Ils₁, Ds₁) ∧
    headArgs k₂ = (.const Ic Ils₂, Ds₂) ∧ Ils₁.map (·.eval ls) = Ils₂.map (·.eval ls) ∧
    ∀ xs : List V, xs.length = n → Q xs →
      Ds₁.map (interp M' ls · xs.reverse) = Ds₂.map (interp M' ls · xs.reverse)

def AuxAgree (M' : CInterp V) (ls : List Nat) (n : Nat) (Q : List V → Prop) (a₁ a₂ : Aux) :
    Prop :=
  a₁.name = a₂.name ∧ KeyAgree M' ls n Q a₁.key a₂.key

theorem find?_forall₂ {α β} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → Option.Rel R (l₁.find? p) (l₂.find? q)
  | [], [], .nil => .none
  | a :: _, b :: _, .cons hab h => by
    simp only [List.find?_cons, ← hpq a b hab]
    cases p a
    · exact find?_forall₂ hpq h
    · exact .some hab

variable {M M' : CInterp V} {ls : List Nat} {tr₁ tr₂ : Translated} {auxRec : List (Name × Name)}
  {ns ms : List Name} {us : List VLevel} {n : Nat} {Q : List V → Prop}

theorem interp_appN_agree {Ic : Name} {Ils₁ Ils₂ : List VLevel} {Ds₁ Ds₂ : List VExpr}
    {ρ : List V} (hl : Ils₁.map (·.eval ls) = Ils₂.map (·.eval ls))
    (hD : Ds₁.map (interp M' ls · ρ) = Ds₂.map (interp M' ls · ρ)) :
    interp M' ls (appN (.const Ic Ils₁) Ds₁) ρ = interp M' ls (appN (.const Ic Ils₂) Ds₂) ρ := by
  rw [interp_appN, interp_appN, hD]
  simp only [interp, hl]

theorem KeyAgree.interp_eq {k₁ k₂ : VExpr} (h : KeyAgree M' ls n Q k₁ k₂) {xs : List V}
    (hl : xs.length = n) (hq : Q xs) :
    interp M' ls k₁ xs.reverse = interp M' ls k₂ xs.reverse := by
  obtain ⟨-, Ic, Ils₁, Ils₂, Ds₁, Ds₂, h₁, h₂, hlv, hD⟩ := h
  rw [← appN_headArgs k₁, ← appN_headArgs k₂, h₁, h₂]
  exact interp_appN_agree hlv (hD xs hl hq)

theorem RestoreHyp.rekey (H : RestoreHyp M M' ls tr₁ auxRec ns ms us n Q)
    (hty : tr₂.types = tr₁.types) (hagree : List.Forall₂ (AuxAgree M' ls n Q) tr₁.aux tr₂.aux) :
    RestoreHyp M M' ls tr₂ auxRec ns ms us n Q := by
  have hfind : ∀ c, Option.Rel (AuxAgree M' ls n Q)
      (tr₁.aux.find? (·.name == c)) (tr₂.aux.find? (·.name == c)) := fun c =>
    find?_forall₂ (fun a b h => by rw [h.1]) hagree
  have hctor : ∀ c, Option.Rel (AuxAgree M' ls n Q) (tr₁.auxOfCtor? c) (tr₂.auxOfCtor? c) :=
    fun c => by
      unfold Translated.auxOfCtor?
      rw [hty]
      exact find?_forall₂ (fun a b h => by rw [h.1]) hagree
  have isSome_eq : ∀ {o₁ : Option Aux} {o₂ : Option Aux},
      Option.Rel (AuxAgree M' ls n Q) o₁ o₂ → o₁.isSome = o₂.isSome
    | _, _, .none => rfl
    | _, _, .some _ => rfl
  refine ⟨fun c => ?_, H.ms_ns, H.ms_rec, H.rec_ns, fun a₂ ha₂ => ?_, H.other,
    fun a₂ ha₂ => ?_, fun a₂ ha₂ xs hl hq => ?_, fun c a₂ hc Ic Ils Ds hk xs hl hq => ?_⟩
  · rw [H.ns_iff c, isSome_eq (hfind c), isSome_eq (hctor c)]
  · obtain ⟨-, -, -, -, Ic, -, Ils₂, -, Ds₂, -, h₂, -⟩ := List.Forall₂.forall_exists_r hagree a₂ ha₂
    exact ⟨Ic, Ils₂, Ds₂, h₂⟩
  · obtain ⟨a₁, -, -, hk, -⟩ := List.Forall₂.forall_exists_r hagree a₂ ha₂
    exact hk
  · obtain ⟨a₁, ha₁, hn, hk⟩ := List.Forall₂.forall_exists_r hagree a₂ ha₂
    rw [← hn, H.aux a₁ ha₁ xs hl hq, hk.interp_eq hl hq]
  · have hr := hctor c
    rw [hc] at hr
    obtain ⟨a₁, ha₁, hn, -, Ic', Ils₁, Ils₂, Ds₁, Ds₂, h₁, h₂, hlv, hD⟩ :
        ∃ a₁, tr₁.auxOfCtor? c = some a₁ ∧ AuxAgree M' ls n Q a₁ a₂ := by
      cases h : tr₁.auxOfCtor? c <;> rw [h] at hr <;> cases hr
      exact ⟨_, rfl, by assumption⟩
    rw [hk] at h₂
    cases h₂
    rw [H.ctor c a₁ ha₁ Ic Ils₁ Ds₁ h₁ xs hl hq, hn]
    exact interp_appN_agree hlv (hD xs hl hq)

def SameHead (a₁ a₂ : Aux) : Prop :=
  a₁.name = a₂.name ∧ ∃ Ic Ils₁ Ils₂ Ds₁ Ds₂, headArgs a₁.key = (.const Ic Ils₁, Ds₁) ∧
    headArgs a₂.key = (.const Ic Ils₂, Ds₂)

theorem AuxAgree.sameHead {a₁ a₂ : Aux} (h : AuxAgree M' ls n Q a₁ a₂) : SameHead a₁ a₂ := by
  obtain ⟨hn, -, Ic, Ils₁, Ils₂, Ds₁, Ds₂, h₁, h₂, -⟩ := h
  exact ⟨hn, Ic, Ils₁, Ils₂, Ds₁, Ds₂, h₁, h₂⟩

theorem Nested.ScopeHyp.rekey {P P' : Name → Prop} (H : Nested.ScopeHyp tr₁ auxRec ns ms n P P')
    (hty : tr₂.types = tr₁.types) (hsame : List.Forall₂ SameHead tr₁.aux tr₂.aux)
    (hkey : ∀ a ∈ tr₂.aux, Scoped P' n a.key) : Nested.ScopeHyp tr₂ auxRec ns ms n P P' := by
  have hfind : ∀ c, Option.Rel SameHead
      (tr₁.aux.find? (·.name == c)) (tr₂.aux.find? (·.name == c)) := fun c =>
    find?_forall₂ (fun a b h => by rw [h.1]) hsame
  have hctor : ∀ c, Option.Rel SameHead (tr₁.auxOfCtor? c) (tr₂.auxOfCtor? c) := fun c => by
    unfold Translated.auxOfCtor?
    rw [hty]
    exact find?_forall₂ (fun a b h => by rw [h.1]) hsame
  have isSome_eq : ∀ {o₁ o₂ : Option Aux}, Option.Rel SameHead o₁ o₂ → o₁.isSome = o₂.isSome
    | _, _, .none => rfl
    | _, _, .some _ => rfl
  refine ⟨fun c => ?_, H.ms_ns, H.ms_rec, H.rec_ns, hkey, fun a₂ ha₂ => ?_,
    fun c a₂ hc Ic Ils Ds hk => ?_, H.fin, H.other⟩
  · rw [H.ns_iff c, isSome_eq (hfind c), isSome_eq (hctor c)]
  · obtain ⟨-, -, -, Ic, -, Ils₂, -, Ds₂, -, h₂⟩ := List.Forall₂.forall_exists_r hsame a₂ ha₂
    exact ⟨Ic, Ils₂, Ds₂, h₂⟩
  · have hr := hctor c
    rw [hc] at hr
    obtain ⟨a₁, ha₁, hn, Ic', Ils₁, Ils₂, Ds₁, Ds₂, h₁, h₂⟩ :
        ∃ a₁, tr₁.auxOfCtor? c = some a₁ ∧ SameHead a₁ a₂ := by
      cases h : tr₁.auxOfCtor? c <;> rw [h] at hr <;> cases hr
      exact ⟨_, rfl, by assumption⟩
    rw [hk] at h₂
    cases h₂
    rw [← hn]
    exact H.ctor c a₁ ha₁ Ic Ils₁ Ds₁ h₁

end Soulgem
