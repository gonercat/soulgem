import Soulgem.Spec.Level

/-! # The level operations of `Spec/Level.lean` evaluate as their meaning -/

namespace Lean4Lean.VLevel

local macro "maxo" : tactic =>
  `(tactic| ((try simp only [Nat.max_def] at *) <;> (repeat' split) <;> omega))

theorem eval_ne_zero_of_isNeverZero {ls : List Nat} {l : VLevel}
    (h : l.isNeverZero = true) : l.eval ls ≠ 0 := by
  induction l with
  | zero | param _ => simp [isNeverZero] at h
  | succ _ => simp [eval]
  | max a b iha ihb =>
    simp only [isNeverZero, Bool.or_eq_true] at h
    simp only [eval]
    intro h0
    have h1 : eval ls a ≤ (eval ls a).max (eval ls b) := Nat.le_max_left _ _
    have h2 : eval ls b ≤ (eval ls a).max (eval ls b) := Nat.le_max_right _ _
    rcases h with h | h
    · exact iha h (by omega)
    · exact ihb h (by omega)
  | imax a b _ ihb =>
    simp only [isNeverZero] at h
    simp only [eval, Lean.Nat.imax]
    have := ihb h
    maxo

end Lean4Lean.VLevel

namespace Lean4Lean.VLevel
#guard (VLevel.max (.param 0) (.param 1)).instK [.zero, .zero] == .zero
#guard (VLevel.imax (.param 0) (.param 1)).instK [.succ .zero, .param 0] == .param 0
#guard (VLevel.imax (.param 0) (.param 1)).instK [.succ .zero, .succ (.param 0)] ==
  .max (.succ .zero) (.succ (.param 0))
#guard (VLevel.max (.param 0) (.succ .zero)).instK [.succ (.param 0)] ==
  .max (.succ (.param 0)) (.succ .zero)

end Lean4Lean.VLevel
