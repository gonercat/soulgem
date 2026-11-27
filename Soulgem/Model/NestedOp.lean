import Soulgem.Model.BlockOp
import Soulgem.Model.Level

/-! # Nested blocks: comparing two block operators -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem

universe u
variable {V : Type u} [SetTheory V]

theorem ffit_nil_iff {M : CInterp V} {ls : List Nat} {X : Nat → V} {ρ xs : List V} :
    FFit M ls X [] ρ xs ↔ xs = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem ffit_cons_iff {M : CInterp V} {ls : List Nat} {X : Nat → V} {f : SField}
    {fs : List SField} {ρ : List V} {x : V} {xs : List V} :
    FFit M ls X (f :: fs) ρ (x :: xs) ↔ x ∈ˢ fdom M ls X f ρ ∧ FFit M ls X fs (x :: ρ) xs := by
  constructor
  · intro h; cases h with | cons hx hr => exact ⟨hx, hr⟩
  · rintro ⟨hx, hr⟩; exact .cons hx hr

theorem not_ffit_cons_nil {M : CInterp V} {ls : List Nat} {X : Nat → V} {f : SField}
    {fs : List SField} {ρ : List V} : ¬ FFit M ls X (f :: fs) ρ [] := fun h => by cases h

theorem ffit_congr {M₁ M₂ : CInterp V} {ls₁ ls₂ : List Nat} {X₁ X₂ : Nat → V} :
    ∀ (fs₁ fs₂ : List SField) (ρ₁ ρ₂ : List V), fs₁.length = fs₂.length →
      (∀ k < fs₁.length, ∀ ys : List V, ys.length = k → FFit M₁ ls₁ X₁ (fs₁.take k) ρ₁ ys →
        FFit M₂ ls₂ X₂ (fs₂.take k) ρ₂ ys →
        fdom M₁ ls₁ X₁ fs₁[k]! (ys.reverse ++ ρ₁) = fdom M₂ ls₂ X₂ fs₂[k]! (ys.reverse ++ ρ₂)) →
      ∀ xs, FFit M₁ ls₁ X₁ fs₁ ρ₁ xs ↔ FFit M₂ ls₂ X₂ fs₂ ρ₂ xs
  | [], [], _, _, _, _, xs => by rw [ffit_nil_iff, ffit_nil_iff]
  | [], _ :: _, _, _, h, _, _ => absurd h (by simp)
  | _ :: _, [], _, _, h, _, _ => absurd h (by simp)
  | f :: fs, g :: gs, ρ₁, ρ₂, hlen, h, xs => by
    have h0 : fdom M₁ ls₁ X₁ f ρ₁ = fdom M₂ ls₂ X₂ g ρ₂ := by
      simpa using h 0 (by simp) [] rfl (by simpa using (FFit.nil : FFit M₁ ls₁ X₁ [] ρ₁ []))
        (by simpa using (FFit.nil : FFit M₂ ls₂ X₂ [] ρ₂ []))
    cases xs with
    | nil => exact ⟨fun h' => absurd h' not_ffit_cons_nil, fun h' => absurd h' not_ffit_cons_nil⟩
    | cons x xs =>
      rw [ffit_cons_iff, ffit_cons_iff, ← h0]
      refine and_congr_right fun hx => ffit_congr fs gs (x :: ρ₁) (x :: ρ₂)
        (by simpa using hlen) (fun k hk ys hys hfit hfit₂ => ?_) xs
      have hx₂ : x ∈ˢ fdom M₂ ls₂ X₂ g ρ₂ := h0 ▸ hx
      have := h (k + 1) (by simpa using hk) (x :: ys) (by simp [hys])
        (by simpa using (FFit.cons hx hfit : FFit M₁ ls₁ X₁ (f :: fs.take k) ρ₁ (x :: ys)))
        (by simpa using (FFit.cons hx₂ hfit₂ : FFit M₂ ls₂ X₂ (g :: gs.take k) ρ₂ (x :: ys)))
      simpa using this

section Fib
variable {M₁ M₂ : CInterp V} {ls₁ ls₂ : List Nat} {b₁ b₂ : SBlock} {ρ₁ ρ₂ : List V}
  {X₁ X₂ : Nat → V} {m₁ m₂ : Nat}

structure CtorCorr (M₁ M₂ : CInterp V) (ls₁ ls₂ : List Nat) (b₁ b₂ : SBlock) (ρ₁ ρ₂ : List V)
    (X₁ X₂ : Nat → V) (m₁ m₂ : Nat) : Prop where
  length : (ctorsOf b₁ m₁).length = (ctorsOf b₂ m₂).length
  fit : ∀ q (hq : q < (ctorsOf b₁ m₁).length) fs,
    FFit M₁ ls₁ X₁ ((ctorsOf b₁ m₁)[q]).fields ρ₁ fs ↔
      FFit M₂ ls₂ X₂ ((ctorsOf b₂ m₂)[q]'(length ▸ hq)).fields ρ₂ fs
  idx : ∀ q (hq : q < (ctorsOf b₁ m₁).length) fs,
    FFit M₁ ls₁ X₁ ((ctorsOf b₁ m₁)[q]).fields ρ₁ fs →
      cidx M₁ ls₁ ρ₁ ((ctorsOf b₁ m₁)[q]) fs = cidx M₂ ls₂ ρ₂ ((ctorsOf b₂ m₂)[q]'(length ▸ hq)) fs

theorem CtorCorr.built (H : CtorCorr M₁ M₂ ls₁ ls₂ b₁ b₂ ρ₁ ρ₂ X₁ X₂ m₁ m₂) {i : V} {q : Nat}
    {fs : List V} : Built M₁ ls₁ b₁ ρ₁ X₁ m₁ i q fs ↔ Built M₂ ls₂ b₂ ρ₂ X₂ m₂ i q fs := by
  constructor
  · rintro ⟨c, hc, hf, hi⟩
    have hq : q < (ctorsOf b₁ m₁).length := (List.getElem?_eq_some_iff.mp hc).1
    have ec : (ctorsOf b₁ m₁)[q] = c := (List.getElem?_eq_some_iff.mp hc).2
    subst ec
    exact ⟨_, List.getElem?_eq_getElem (H.length ▸ hq), (H.fit q hq fs).mp hf,
      (H.idx q hq fs hf).symm.trans hi⟩
  · rintro ⟨c, hc, hf, hi⟩
    have hq₂ : q < (ctorsOf b₂ m₂).length := (List.getElem?_eq_some_iff.mp hc).1
    have hq : q < (ctorsOf b₁ m₁).length := H.length ▸ hq₂
    have ec : (ctorsOf b₂ m₂)[q] = c := (List.getElem?_eq_some_iff.mp hc).2
    subst ec
    have hf' := (H.fit q hq fs).mpr hf
    exact ⟨_, List.getElem?_eq_getElem hq, hf', (H.idx q hq fs hf').trans hi⟩

theorem fib_congr (hlev : lev ls₁ b₁ = lev ls₂ b₂)
    (H : CtorCorr M₁ M₂ ls₁ ls₂ b₁ b₂ ρ₁ ρ₂ X₁ X₂ m₁ m₂) (i : V) :
    fib M₁ ls₁ b₁ ρ₁ X₁ m₁ i = fib M₂ ls₂ b₂ ρ₂ X₂ m₂ i := by
  apply SetTheory.ext; intro x
  by_cases h0 : lev ls₁ b₁ = 0
  · rw [mem_fib_zero h0, mem_fib_zero (hlev ▸ h0)]
    exact and_congr_right fun _ => exists_congr fun q => exists_congr fun fs => H.built
  · rw [mem_fib_pos h0, mem_fib_pos (hlev ▸ h0)]
    exact exists_congr fun q => exists_congr fun fs => and_congr_left fun _ => H.built

theorem app_Φ_congr (hlev : lev ls₁ b₁ = lev ls₂ b₂)
    (H : CtorCorr M₁ M₂ ls₁ ls₂ b₁ b₂ ρ₁ ρ₂ X₁ X₂ m₁ m₂) {i : V}
    (hi₁ : i ∈ˢ Is M₁ ls₁ b₁ ρ₁ m₁) (hi₂ : i ∈ˢ Is M₂ ls₂ b₂ ρ₂ m₂) :
    app (Φ M₁ ls₁ b₁ ρ₁ X₁ m₁) i = app (Φ M₂ ls₂ b₂ ρ₂ X₂ m₂) i := by
  rw [app_Φ hi₁, app_Φ hi₂]; exact fib_congr hlev H i

end Fib

end Soulgem.Nested
