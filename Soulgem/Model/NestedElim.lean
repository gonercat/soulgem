import Soulgem.Spec.Nested

/-! # Nested elimination in the model -/

namespace Soulgem.Spec
open Lean4Lean

def Inv (ts : List UType) (s : NState) : Prop :=
  ts.length ≤ s.newTypes.size ∧ ∀ i (h : i < ts.length),
    (s.newTypes[i]!).name = ts[i].name ∧ (s.newTypes[i]!).type = ts[i].type

def Pres {α : Type} (ts : List UType) (x : NM α) : Prop :=
  ∀ s, Inv ts s → match x.run s with
    | .ok (_, s') => Inv ts s'
    | .error _ => True

namespace Pres
variable {ts : List UType}

theorem pure' {α : Type} (a : α) : Pres ts (pure a : NM α) := fun _ h => h

theorem bind' {α β : Type} {x : NM α} {f : α → NM β} (hx : Pres ts x) (hf : ∀ a, Pres ts (f a)) :
    Pres ts (x >>= f) := fun s hs => by
  have h1 := hx s hs
  simp only [StateT.run_bind]
  revert h1
  cases x.run s with
  | error e => intro; trivial
  | ok p => intro h1; exact hf p.1 p.2 h1

theorem get_bind' {β : Type} {f : NState → NM β} (hf : ∀ s₀, Inv ts s₀ → Pres ts (f s₀)) :
    Pres ts (get >>= f) := fun s hs => by
  simp only [StateT.run_bind, StateT.run_get, pure_bind]; exact hf s hs s hs

theorem modify' {f : NState → NState} (hf : ∀ s, Inv ts s → Inv ts (f s)) :
    Pres ts (modify f : NM Unit) := fun s hs => hf s hs

theorem throw' {α : Type} (e : String) : Pres ts (throw e : NM α) := fun _ _ => trivial

theorem lift' {α : Type} (x : Except String α) : Pres ts (liftM x : NM α) := fun s hs => by
  cases x
  · simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.run, bind, Except.bind]
  · simpa [liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.run, bind, Except.bind, pure,
      Except.pure] using hs

theorem mapM' {α β : Type} {f : α → NM β} (hf : ∀ a, Pres ts (f a)) :
    ∀ l : List α, Pres ts (l.mapM f)
  | [] => by simpa using pure' []
  | a :: l => by
    simp only [List.mapM_cons]
    exact bind' (hf a) fun b => bind' (mapM' hf l) fun _ => pure' _

theorem forIn' {α β : Type} {f : α → β → NM (ForInStep β)} (hf : ∀ a b, Pres ts (f a b)) :
    ∀ (l : List α) (b : β), Pres ts (forIn l b f)
  | [], b => by simpa using pure' b
  | a :: l, b => by
    simp only [List.forIn_cons]
    refine bind' (hf a b) fun r => ?_
    cases r with
    | done b => exact pure' b
    | yield b => exact forIn' hf l b

end Pres

theorem Inv.push {ts : List UType} {s : NState} (h : Inv ts s) (t : UType) :
    Inv ts { s with newTypes := s.newTypes.push t } := by
  refine ⟨by simp; have := h.1; omega, fun i hi => ?_⟩
  have hs : i < s.newTypes.size := by have := h.1; omega
  simp only [getElem!_pos (s.newTypes.push t) i (by simp; omega), Array.getElem_push_lt hs,
    ← getElem!_pos s.newTypes i hs]
  exact h.2 i hi

theorem Inv.set {ts : List UType} {s s₀ : NState} (h : Inv ts s) (h₀ : Inv ts s₀) {i : Nat}
    (hi : i < s₀.newTypes.size) (cs : List (Lean.Name × VExpr)) :
    Inv ts { s with newTypes := s.newTypes.set! i { s₀.newTypes[i] with ctors := cs } } := by
  refine ⟨by simp; exact h.1, fun k hk => ?_⟩
  have hks : k < s.newTypes.size := by have := h.1; omega
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hik : i = k
  · subst hik
    rw [getElem!_pos _ i (by simp; exact hks), Array.getElem_setIfInBounds_self
        (by simp; exact hks)]
    rw [← getElem!_pos s₀.newTypes i hi]; exact h₀.2 i hk
  · rw [getElem!_pos _ k (by simp; exact hks), Array.getElem_setIfInBounds_ne hks hik,
      ← getElem!_pos s.newTypes k hks]
    exact h.2 k hk

variable (ind? : Lean.Name → Option IndInfo) (contains : Lean.Name → Bool) (lvls : List VLevel)
  (n : Nat) {ts : List UType}

theorem uniqueName_pres (base : Lean.Name) : Pres ts (uniqueName contains base) := fun s hs => by
  unfold uniqueName
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases uniqueName.loop contains base 10000 s.nextIdx with
  | error e => simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.run, bind,
      Except.bind]
  | ok p =>
    simp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.run, bind, Except.bind,
      set, StateT.set, pure, Except.pure, StateT.pure]
    exact hs

macro "pres" : tactic => `(tactic| repeat' (first
  | (refine Pres.bind' (uniqueName_pres _ _) fun _ => ?_)
  | exact Pres.pure' _ | exact Pres.throw' _ | exact Pres.lift' _
  | (apply Pres.bind' <;> try intro)
  | (apply Pres.forIn' <;> try intros)
  | (apply Pres.mapM' <;> try intro)
  | (apply Pres.modify'; intro _ h; first | exact h | exact h.push _)
  | split
  | dsimp only))

theorem replaceIfNested_pres (Ps : List VExpr) (d : Nat) (e : VExpr) :
    Pres ts (replaceIfNested ind? contains lvls n Ps d e) := by
  unfold replaceIfNested
  pres

theorem replaceAll_pres (Ps : List VExpr) : ∀ (e : VExpr) (d : Nat),
    Pres ts (replaceAll ind? contains lvls n Ps e d)
  | e, d => by
    unfold replaceAll
    refine Pres.bind' (replaceIfNested_pres ind? contains lvls n Ps d e) fun r => ?_
    split
    · exact Pres.pure' _
    · split <;>
        first
        | exact Pres.pure' _
        | exact Pres.bind' (replaceAll_pres Ps _ _) fun _ =>
            Pres.bind' (replaceAll_pres Ps _ _) fun _ => Pres.pure' _

theorem elimLoop_pres : ∀ (fuel i : Nat), Pres ts (elimLoop ind? contains lvls n fuel i)
  | 0, _ => by unfold elimLoop; exact Pres.throw' _
  | fuel + 1, i => by
    unfold elimLoop
    refine Pres.get_bind' fun s₀ h₀ => ?_
    split
    · rename_i hi
      refine Pres.bind' (Pres.mapM' (fun x => ?_) _) fun cs =>
        Pres.bind' (Pres.modify' fun s h => h.set h₀ hi cs) fun _ => elimLoop_pres fuel (i + 1)
      obtain ⟨c, cty⟩ := x
      dsimp only
      split
      · exact Pres.bind' (replaceAll_pres ind? contains lvls n _ _ _) fun _ => Pres.pure' _
      · exact Pres.throw' _
    · exact Pres.pure' _

theorem elim_prefix {u : UDecl} {tr : Translated} (h : elim ind? contains u = .ok tr) :
    u.types.length ≤ tr.types.length ∧ ∀ i (hi : i < u.types.length),
      (tr.types[i]!).name = u.types[i].name ∧ (tr.types[i]!).type = u.types[i].type := by
  unfold elim at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i v heq
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hg := elimLoop_pres ind? contains ((List.range u.uvars).map VLevel.param) u.nparams
      (ts := u.types) 100000 0 { newTypes := u.types.toArray }
      ⟨by simp, fun i hi => by simp [getElem!_pos u.types.toArray i (by simpa using hi)]⟩
    rw [heq] at hg
    obtain ⟨hl, hk⟩ := hg
    refine ⟨by simpa using hl, fun i hi => ?_⟩
    have := hk i hi
    rwa [← Array.getElem!_toList] at this

theorem elim_length {u : UDecl} {tr : Translated} (h : elim ind? contains u = .ok tr) :
    u.types.length ≤ tr.types.length :=
  (elim_prefix ind? contains h).1

end Soulgem.Spec
