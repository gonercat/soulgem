import Soulgem.Model.Tele
import Soulgem.Spec.Nested

/-! # Telescopes, contexts and agreement -/

namespace Soulgem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V] {M M' : CInterp V} {ls : List Nat}

theorem Sat.of_ext {Γ : List VExpr} {ρ : List V} (hΓ : Sat M ls Γ ρ) :
    ∀ {As : List VExpr} {xs : List V},
    Ext M ls As ρ xs → Sat M ls (As.reverse ++ Γ) (xs.reverse ++ ρ)
  | [], [], .nil => hΓ
  | A :: As, x :: xs, .cons hx hxs => by
    have := Sat.of_ext (Γ := A :: Γ) (ρ := x :: ρ) ⟨hΓ, hx⟩ hxs
    simpa using this

theorem Ext.of_sat {Γ : List VExpr} {ρ : List V} : ∀ {As : List VExpr} {xs : List V},
    xs.length = As.length → Sat M ls (As.reverse ++ Γ) (xs.reverse ++ ρ) →
    Sat M ls Γ ρ ∧ Ext M ls As ρ xs
  | [], [], _, h => ⟨by simpa using h, .nil⟩
  | A :: As, x :: xs, hl, h => by
    have h' : Sat M ls (As.reverse ++ (A :: Γ)) (xs.reverse ++ (x :: ρ)) := by simpa using h
    obtain ⟨⟨hΓ, hx⟩, hxs⟩ := Ext.of_sat (by simpa using hl) h'
    exact ⟨hΓ, .cons hx hxs⟩

theorem Ext.get : ∀ {As : List VExpr} {ρ xs : List V}, Ext M ls As ρ xs →
    ∀ l (h1 : l < As.length) (h2 : l < xs.length),
      xs[l] ∈ˢ interp M ls As[l] ((xs.take l).reverse ++ ρ)
  | _, _, _, .cons hx _, 0, _, _ => by simpa using hx
  | _, _, _, .cons _ hxs, l + 1, h1, h2 => by
    have := hxs.get l (by simpa using h1) (by simpa using h2)
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this

theorem Ext.of_get : ∀ {As : List VExpr} {ρ xs : List V}, xs.length = As.length →
    (∀ l (h1 : l < As.length) (h2 : l < xs.length),
      xs[l] ∈ˢ interp M ls As[l] ((xs.take l).reverse ++ ρ)) → Ext M ls As ρ xs
  | [], _, [], _, _ => .nil
  | A :: As, ρ, x :: xs, hl, h => by
    refine .cons (by have := h 0 (by simp) (by simp); simpa using this)
      (Ext.of_get (by simpa using hl) fun l h1 h2 => ?_)
    have := h (l + 1) (by simpa using h1) (by simpa using h2)
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this

theorem ConstsIn.and {P Q : Name → Prop} : ∀ {e : VExpr}, ConstsIn P e → ConstsIn Q e →
    ConstsIn (fun c => P c ∧ Q c) e
  | .bvar _, _, _ | .sort _, _, _ => trivial
  | .const _ _, h1, h2 => ⟨h1, h2⟩
  | .app .., h1, h2 | .lam .., h1, h2 | .forallE .., h1, h2 => ⟨h1.1.and h2.1, h1.2.and h2.2⟩

theorem constsIn_of_mentions {ns : List Name} : ∀ {e : VExpr}, mentions ns e = false →
    ConstsIn (fun c => c ∉ ns) e
  | .bvar _, _ | .sort _, _ => trivial
  | .const c _, h => by simp only [ConstsIn]; simpa [mentions] using h
  | .app f a, h => by
    simp only [mentions, Bool.or_eq_false_iff] at h
    exact ⟨constsIn_of_mentions h.1, constsIn_of_mentions h.2⟩
  | .lam A b, h | .forallE A b, h => by
    simp only [mentions, Bool.or_eq_false_iff] at h
    exact ⟨constsIn_of_mentions h.1, constsIn_of_mentions h.2⟩

theorem Ext.congrM {P : Name → Prop} (hag : ∀ c, P c → M c = M' c) :
    ∀ {As : List VExpr} {ρ xs : List V}, (∀ A ∈ As, ConstsIn P A) →
    (Ext M ls As ρ xs ↔ Ext M' ls As ρ xs)
  | [], ρ, xs, _ => by simp [Ext_nil_iff]
  | A :: As, ρ, xs, h => by
    simp only [Ext_cons_iff]
    rw [interp_congr ((h A (.head _)).mono hag)]
    constructor
    · intro ⟨x, xs', e, hx, hxs⟩
      exact ⟨x, xs', e, hx, (Ext.congrM hag fun B hB => h B (.tail _ hB)).mp hxs⟩
    · intro ⟨x, xs', e, hx, hxs⟩
      exact ⟨x, xs', e, hx, (Ext.congrM hag fun B hB => h B (.tail _ hB)).mpr hxs⟩

theorem piTel_congrM {P : Name → Prop} (hag : ∀ c, P c → M c = M' c) {B : List V → V} :
    ∀ {As : List VExpr} {ρ : List V}, (∀ A ∈ As, ConstsIn P A) →
    piTel M ls As B ρ = piTel M' ls As B ρ
  | [], _, _ => rfl
  | A :: As, ρ, h => by
    simp only [piTel]
    rw [interp_congr ((h A (.head _)).mono hag)]
    congr 1; funext x
    exact piTel_congrM hag fun C hC => h C (.tail _ hC)

theorem piTel_congr {B B' : List V → V} : ∀ {As : List VExpr} {ρ : List V},
    (∀ xs, Ext M ls As ρ xs → B (xs.reverse ++ ρ) = B' (xs.reverse ++ ρ)) →
    piTel M ls As B ρ = piTel M ls As B' ρ
  | [], ρ, h => h [] .nil
  | A :: As, ρ, h => by
    simp only [piTel]
    exact cpi_congr fun x hx => piTel_congr fun xs hxs => by
      have := h (x :: xs) (.cons hx hxs); simpa using this

theorem lamTel_congrM' {P : Name → Prop} (hag : ∀ c, P c → M c = M' c) {body : List V → V} :
    ∀ {As : List VExpr} {ρ : List V}, (∀ A ∈ As, ConstsIn P A) →
    Soulgem.lamTel M ls As body ρ = Soulgem.lamTel M' ls As body ρ
  | [], _, _ => rfl
  | A :: As, ρ, h => by
    simp only [Soulgem.lamTel]
    rw [interp_congr ((h A (.head _)).mono hag)]
    congr 1; funext x
    exact lamTel_congrM' hag fun C hC => h C (.tail _ hC)

end Soulgem
