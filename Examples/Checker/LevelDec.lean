import Soulgem.Spec.WF
import Soulgem.Model.Level

/-! # Deciding level inequality (`leN`) and equivalence (`levelEqB`) -/

namespace Soulgem.Checker
open Lean4Lean Soulgem.Spec

def mkMax (a b : VLevel) : VLevel :=
  if a = .zero then b else if b = .zero then a else if a = b then a else .max a b

theorem eval_mkMax (a b : VLevel) (ls : List Nat) :
    (mkMax a b).eval ls = Nat.max (a.eval ls) (b.eval ls) := by
  unfold mkMax
  split
  · subst_vars; simp [VLevel.eval]
  · split
    · subst_vars; simp [VLevel.eval]
    · split
      · subst_vars; simp
      · rfl

def imaxGen (a b : VLevel) : VLevel := if a = .zero then b else if a = b then b else .imax a b

theorem eval_imaxGen (a b : VLevel) (ls : List Nat) :
    (imaxGen a b).eval ls = Lean.Nat.imax (a.eval ls) (b.eval ls) := by
  unfold imaxGen
  split
  · subst_vars; simp only [VLevel.eval, Lean.Nat.imax]; split <;> simp_all
  · split
    · subst_vars; simp only [Lean.Nat.imax]; split <;> simp_all
    · rfl

/-- `imax a b`, simplified: `imax a 0 = 0`, `imax a (b+1) = max a (b+1)`. -/
def imaxN (a : VLevel) : VLevel → VLevel
  | .zero => .zero
  | b => if b.isNeverZero then mkMax a b else imaxGen a b

theorem eval_imaxN (a b : VLevel) (ls : List Nat) :
    (imaxN a b).eval ls = Lean.Nat.imax (a.eval ls) (b.eval ls) := by
  cases b with
  | zero => simp [imaxN, VLevel.eval, Lean.Nat.imax]
  | succ _ | param _ | max _ _ | imax _ _ =>
    simp only [imaxN]
    split
    · rename_i h
      have := VLevel.eval_ne_zero_of_isNeverZero (ls := ls) h
      rw [eval_mkMax]; simp only [Lean.Nat.imax]; split <;> omega
    · exact eval_imaxGen _ _ _

/-- `l + 1` pushed through `max`. -/
def succN : VLevel → VLevel
  | .max a b => mkMax (succN a) (succN b)
  | l => .succ l

theorem eval_succN : ∀ (l : VLevel) (ls : List Nat), (succN l).eval ls = l.eval ls + 1
  | .max a b, ls => by
    simp only [succN, eval_mkMax, eval_succN a ls, eval_succN b ls, VLevel.eval]
    exact (Nat.succ_max_succ _ _)
  | .zero, _ | .param _, _ | .succ _, _ | .imax _ _, _ => rfl

/-- An eval-preserving simplification of levels. -/
def lnorm : VLevel → VLevel
  | .zero => .zero
  | .param i => .param i
  | .succ l => succN (lnorm l)
  | .max a b => mkMax (lnorm a) (lnorm b)
  | .imax a b => imaxN (lnorm a) (lnorm b)

theorem eval_lnorm : ∀ (l : VLevel) (ls : List Nat), (lnorm l).eval ls = l.eval ls
  | .zero, _ | .param _, _ => rfl
  | .succ l, ls => by simp [lnorm, VLevel.eval, eval_succN, eval_lnorm l ls]
  | .max a b, ls => by simp [lnorm, VLevel.eval, eval_mkMax, eval_lnorm a ls, eval_lnorm b ls]
  | .imax a b, ls => by simp [lnorm, VLevel.eval, eval_imaxN, eval_lnorm a ls, eval_lnorm b ls]

/-- Sound `a ≤ b` under every assignment, by fuel. -/
def leBf : Nat → VLevel → VLevel → Bool
  | 0, a, b => decide (a = b) || decide (a = .zero)
  | n + 1, a, b =>
    decide (a = b) || decide (a = .zero) ||
    (match a, b with
     | .succ a', .succ b' => leBf n a' b'
     | .max x y, b => leBf n x b && leBf n y b
     | .imax x y, b => leBf n x b && leBf n y b
     | _, _ => false) ||
    (match b with
     | .succ b' => leBf n a b'
     | .max x y => leBf n a x || leBf n a y
     | .imax _ y => leBf n a y
     | _ => false)

def lsize : VLevel → Nat
  | .zero | .param _ => 1
  | .succ l => lsize l + 1
  | .max a b | .imax a b => lsize a + lsize b + 1

def leB (a b : VLevel) : Bool := leBf (lsize a + lsize b) a b

theorem imax_le_max (x y : Nat) : Lean.Nat.imax x y ≤ Nat.max x y := by
  unfold Lean.Nat.imax; split <;> omega

theorem leBf_sound : ∀ (n : Nat) {a b : VLevel}, leBf n a b = true → LevelLE a b
  | 0, a, b, h => by
    simp only [leBf, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | rfl
    · exact fun _ => Nat.le_refl _
    · exact fun _ => Nat.zero_le _
  | n + 1, a, b, h => by
    simp only [leBf, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with ((rfl | rfl) | h) | h
    · exact fun _ => Nat.le_refl _
    · exact fun _ => Nat.zero_le _
    · split at h
      · intro ls; have := leBf_sound n h ls; simp only [VLevel.eval]; omega
      · simp only [Bool.and_eq_true] at h
        intro ls; have h1 := leBf_sound n h.1 ls; have h2 := leBf_sound n h.2 ls
        simp only [VLevel.eval]; exact Nat.max_le.mpr ⟨h1, h2⟩
      · simp only [Bool.and_eq_true] at h
        intro ls; have h1 := leBf_sound n h.1 ls; have h2 := leBf_sound n h.2 ls
        simp only [VLevel.eval]
        exact Nat.le_trans (imax_le_max _ _) (Nat.max_le.mpr ⟨h1, h2⟩)
      · cases h
    · split at h
      · intro ls; have := leBf_sound n h ls; simp only [VLevel.eval]; omega
      · simp only [Bool.or_eq_true] at h
        intro ls; simp only [VLevel.eval]
        rcases h with h | h
        · exact Nat.le_trans (leBf_sound n h ls) (Nat.le_max_left _ _)
        · exact Nat.le_trans (leBf_sound n h ls) (Nat.le_max_right _ _)
      · intro ls; have := leBf_sound n h ls; simp only [VLevel.eval, Lean.Nat.imax]
        split
        · rename_i h0; rw [h0] at this; exact this
        · exact Nat.le_trans this (Nat.le_max_right _ _)
      · cases h

theorem leB_sound {a b : VLevel} (h : leB a b = true) : LevelLE a b := leBf_sound _ h

def lparams : VLevel → List Nat
  | .zero => []
  | .param i => [i]
  | .succ l => lparams l
  | .max a b | .imax a b => lparams a ++ lparams b

def substP (p : Nat) (v : VLevel) : VLevel → VLevel
  | .zero => .zero
  | .param i => if i = p then v else .param i
  | .succ l => .succ (substP p v l)
  | .max a b => .max (substP p v a) (substP p v b)
  | .imax a b => .imax (substP p v a) (substP p v b)

theorem eval_substP {p : Nat} {v : VLevel} {ls : List Nat} (hp : p < ls.length) :
    ∀ l : VLevel, (substP p v l).eval ls = l.eval (ls.set p (v.eval ls))
  | .zero => rfl
  | .param i => by
    simp only [substP, VLevel.eval]
    split
    · subst_vars; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hp]
    · rename_i h; simp [VLevel.eval, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]
  | .succ l => by simp [substP, VLevel.eval, eval_substP hp l]
  | .max a b | .imax a b => by simp [substP, VLevel.eval, eval_substP hp a, eval_substP hp b]

theorem eval_substP_zero {p : Nat} {ls : List Nat} (h0 : ls.getD p 0 = 0) :
    ∀ l : VLevel, (substP p .zero l).eval ls = l.eval ls
  | .zero => rfl
  | .param i => by
    simp only [substP, VLevel.eval]
    split
    · subst_vars; simp only [VLevel.eval]; exact h0.symm
    · rfl
  | .succ l => by simp [substP, VLevel.eval, eval_substP_zero h0 l]
  | .max a b | .imax a b => by
    simp [substP, VLevel.eval, eval_substP_zero h0 a, eval_substP_zero h0 b]

/-- `leB` after `lnorm`, splitting listed parameters into `0` and `p + 1`. -/
def leSplit : List Nat → VLevel → VLevel → Bool
  | [], a, b => leB (lnorm a) (lnorm b)
  | p :: ps, a, b =>
    leSplit ps (substP p .zero a) (substP p .zero b) &&
    leSplit ps (substP p (.succ (.param p)) a) (substP p (.succ (.param p)) b)

theorem leSplit_sound : ∀ (ps : List Nat) {a b : VLevel}, leSplit ps a b = true → LevelLE a b
  | [], a, b, h => fun ls => by
    have := leB_sound h ls; rwa [eval_lnorm, eval_lnorm] at this
  | p :: ps, a, b, h => fun ls => by
    simp only [leSplit, Bool.and_eq_true] at h
    cases hx : ls.getD p 0 with
    | zero =>
      have := leSplit_sound ps h.1 ls
      rwa [eval_substP_zero hx, eval_substP_zero hx] at this
    | succ y =>
      have hp : p < ls.length :=
        match Nat.decLt p ls.length with
        | .isTrue h => h
        | .isFalse h' => by
          have : ls[p]? = none := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt h')
          rw [List.getD_eq_getElem?_getD, this] at hx
          exact absurd hx (Nat.noConfusion ·)
      have hls : ls.set p (y + 1) = ls := by
        have hx' : ls[p] = y + 1 := by
          simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp] using hx
        rw [← hx']; exact List.set_getElem_self hp
      have hp' : p < (ls.set p y).length := by simpa using hp
      have := leSplit_sound ps h.2 (ls.set p y)
      have hv : (VLevel.succ (.param p)).eval (ls.set p y) = y + 1 := by
        simp [VLevel.eval, List.getD_eq_getElem?_getD, List.getElem?_set_self hp]
      rw [eval_substP hp', eval_substP hp', hv, List.set_set, hls] at this
      exact this

/-- A sound decision of `a ≤ b` under every assignment. -/
def leN (a b : VLevel) : Bool := leSplit (lparams a ++ lparams b).eraseDups a b

theorem leN_sound {a b : VLevel} (h : leN a b = true) : LevelLE a b := leSplit_sound _ h

/-- Level equivalence: equal after `lnorm`, or `leN` both ways. -/
def levelEqB (a b : VLevel) : Bool := decide (lnorm a = lnorm b) || (leN a b && leN b a)

theorem levelEqB_sound {a b : VLevel} (h : levelEqB a b = true) : a ≈ b := by
  unfold levelEqB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with he | ⟨h1, h2⟩
  · exact funext fun ls => by rw [← eval_lnorm a ls, he, eval_lnorm]
  · exact funext fun ls => Nat.le_antisymm (leN_sound h1 ls) (leN_sound h2 ls)

end Soulgem.Checker
