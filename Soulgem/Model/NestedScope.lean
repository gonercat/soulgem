import Soulgem.Model.BlockScope
import Soulgem.Model.Restore

/-! # Restoration preserves scoping -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

theorem closedN_appN_iff {k : Nat} {f : VExpr} {as : List VExpr} :
    (appN f as).ClosedN k ↔ f.ClosedN k ∧ ∀ a ∈ as, a.ClosedN k :=
  ⟨fun h => ⟨closedN_appN_args.closedN_appN_head h, closedN_appN_args h⟩,
    fun h => closedN_appN_of h.1 h.2⟩

theorem scoped_appN_iff {P : Name → Prop} {k : Nat} {f : VExpr} {as : List VExpr} :
    Scoped P k (appN f as) ↔ Scoped P k f ∧ ∀ a ∈ as, Scoped P k a := by
  unfold Scoped
  rw [closedN_appN_iff, constsIn_appN]
  exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3⟩, fun a ha => ⟨h2 a ha, h4 a ha⟩⟩,
    fun ⟨⟨h1, h3⟩, h⟩ => ⟨⟨h1, fun a ha => (h a ha).1⟩, h3, fun a ha => (h a ha).2⟩⟩

theorem scoped_spine {P : Name → Prop} {k : Nat} {t h : VExpr} {args : List VExpr}
    (hh : headArgs t = (h, args)) (ht : Scoped P k t) : Scoped P k h ∧ ∀ a ∈ args,
        Scoped P k a := by
  have := appN_headArgs t
  rw [hh] at this
  rw [← this] at ht
  exact scoped_appN_iff.mp ht

structure ScopeHyp (tr : Translated) (auxRec : List (Name × Name)) (ns ms : List Name) (n : Nat)
    (P P' : Name → Prop) : Prop where
  ns_iff : ∀ c, c ∈ ns ↔ ((tr.aux.find? (·.name == c)).isSome ∨ (tr.auxOfCtor? c).isSome)
  ms_ns : ∀ c ∈ ns, c ∈ ms
  ms_rec : ∀ p ∈ auxRec, p.1 ∈ ms
  rec_ns : ∀ p ∈ auxRec, p.1 ∉ ns
  key : ∀ a ∈ tr.aux, Scoped P' n a.key
  key_head : ∀ a ∈ tr.aux, ∃ Ic Ils Ds, headArgs a.key = (.const Ic Ils, Ds)
  ctor : ∀ c a, tr.auxOfCtor? c = some a → ∀ Ic Ils Ds, headArgs a.key = (.const Ic Ils, Ds) →
    P' (c.replacePrefix a.name Ic)
  fin : ∀ p ∈ auxRec, P' p.2
  other : ∀ c, P c → c ∉ ns → (∀ p ∈ auxRec, p.1 ≠ c) → P' c

variable {tr : Translated} {auxRec : List (Name × Name)} {ns ms : List Name} {n : Nat}
  {P P' : Name → Prop} {us : List VLevel}

namespace ScopeHyp
variable (H : ScopeHyp tr auxRec ns ms n P P')
include H

theorem names : RestoreNames tr auxRec ns := ⟨H.ns_iff, H.rec_ns, H.key_head⟩

theorem free {k : Nat} {e : VExpr} (he : Scoped P k e) (hm : mentions ms e = false) :
    Scoped P' k e :=
  ⟨he.1, (he.2.and (constsIn_of_mentions hm)).mono fun c ⟨hP, hc⟩ =>
    H.other c hP (fun h => hc (H.ms_ns c h)) fun p hp hpc => hc (hpc ▸ H.ms_rec p hp)⟩

theorem place_key {a : Aux} (ha : a ∈ tr.aux) {d : Nat} (hn : n ≤ d) :
    Scoped P' d (place n id d a.key) :=
  Scoped.place (H.key a ha) fun L hL => by simp only [id]; omega

theorem aux_case {t : VExpr} {d : Nat} (hn : n ≤ d) (ht : Scoped P d t) {c : Name}
    {us' : List VLevel} {args : List VExpr} {a : Aux} (hh : headArgs t = (.const c us', args))
    (ha : tr.aux.find? (·.name == c) = some a) (hrest : ∀ x ∈ args.drop n, mentions ms x = false) :
    Scoped P' d (appN (place n id d a.key) (args.drop n)) :=
  scoped_appN_iff.mpr ⟨H.place_key (List.mem_of_find?_eq_some ha) hn, fun x hx =>
    H.free ((scoped_spine hh ht).2 x (List.mem_of_mem_drop hx)) (hrest x hx)⟩

theorem ctor_case {t : VExpr} {d : Nat} (hn : n ≤ d) (ht : Scoped P d t) {c : Name}
    {us' : List VLevel} {args : List VExpr} {a : Aux} {Ic : Name} {Ils : List VLevel}
    {Ds : List VExpr} (hh : headArgs t = (.const c us', args)) (hc : tr.auxOfCtor? c = some a)
    (hk : headArgs (place n id d a.key) = (.const Ic Ils, Ds))
    (hrest : ∀ x ∈ args.drop n, mentions ms x = false) :
    Scoped P' d (appN (.const (c.replacePrefix a.name Ic) Ils) (Ds ++ args.drop n)) := by
  have ha := List.mem_of_find?_eq_some hc
  obtain ⟨Ic₀, Ils₀, Ds₀, hk0, hkp⟩ := H.names.place_head ha n d
  rw [hk] at hkp
  simp only [Prod.mk.injEq, VExpr.const.injEq] at hkp
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hkp
  refine scoped_appN_iff.mpr ⟨⟨trivial, H.ctor c a hc _ _ _ hk0⟩, fun x hx => ?_⟩
  rcases List.mem_append.mp hx with hx | hx
  · have := appN_headArgs (place n id d a.key)
    rw [hk] at this
    exact (scoped_appN_iff.mp (this ▸ H.place_key ha hn)).2 x hx
  · exact H.free ((scoped_spine hh ht).2 x (List.mem_of_mem_drop hx)) (hrest x hx)

theorem scoped_restoreBody (e : VExpr) {d : Nat} (hn : n ≤ d)
    (hs : restoreSafe ns ms us n e d = true) (he : Scoped P d e) :
    Scoped P' d (tr.restoreBody auxRec n e d) := by
  refine H.names.induction (us := us) (ms := ms)
    (fun d e e' => Scoped P d e → Scoped P' d e')
    (fun _ _ _ he => ⟨he.1, trivial⟩) (fun _ _ _ _ => ⟨trivial, trivial⟩)
    (fun _ _ _ _ _ _ hn hh ha _ _ hrest he => H.aux_case hn he hh ha hrest)
    (fun _ _ _ _ _ _ _ _ _ hn hh hct hk _ _ hrest he => H.ctor_case hn he hh hct hk hrest)
    (fun _ _ _ p _ _ hp _ => ⟨trivial, H.fin p (List.mem_of_find?_eq_some hp)⟩)
    (fun _ c _ _ hc hp he => ⟨trivial, H.other c he.2 hc fun p hpm hpc => by
      have := List.find?_eq_none.mp hp p hpm; simp [hpc] at this⟩)
    (fun _ _ _ _ _ _ hA hb he =>
      let hA := hA ⟨he.1.1, he.2.1⟩; let hb := hb ⟨he.1.2, he.2.2⟩
      ⟨⟨hA.1, hb.1⟩, hA.2, hb.2⟩)
    (fun _ _ _ _ _ _ hA hb he =>
      let hA := hA ⟨he.1.1, he.2.1⟩; let hb := hb ⟨he.1.2, he.2.2⟩
      ⟨⟨hA.1, hb.1⟩, hA.2, hb.2⟩)
    (fun _ _ _ _ _ _ hf hx he =>
      let hf := hf ⟨he.1.1, he.2.1⟩; let hx := hx ⟨he.1.2, he.2.2⟩
      ⟨⟨hf.1, hx.1⟩, hf.2, hx.2⟩)
    e hn hs he

end ScopeHyp
end Soulgem.Nested
