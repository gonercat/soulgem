import Soulgem.CoreDecls
import Soulgem.Quot

/-!
# A model of Lean's core logic

The constants `Eq`, `Iff`, `Nonempty`, the quotient primitives and the axioms `propext`,
`Classical.choice`, `Quot.sound`.
-/

namespace Soulgem.Core
open ConLeche ConLeche.SetTheory Lean4Lean Soulgem

universe u
variable {V : Type u} [SetTheory V]

/-! ## Set-level ingredients -/

open Classical in
noncomputable def eps (A : V) : V := if h : ∃ x, x ∈ˢ A then Classical.choose h else pt

theorem eps_mem {A x : V} (h : x ∈ˢ A) : eps A ∈ˢ A := by
  have h' : ∃ x, x ∈ˢ A := ⟨x, h⟩
  unfold eps; rw [dite_eq_left h']; exact Classical.choose_spec h'

inductive EqvC (R : V → V → Prop) : V → V → Prop where
  | rel {a b} : R a b → EqvC R a b
  | refl {a} : EqvC R a a
  | symm {a b} : EqvC R a b → EqvC R b a
  | trans {a b c} : EqvC R a b → EqvC R b c → EqvC R a c

def QRel (α r x y : V) : Prop := x ∈ˢ α ∧ y ∈ˢ α ∧ (pt : V) ∈ˢ app (app r x) y

noncomputable def cls (α r a : V) : V := sep α (EqvC (QRel α r) a)

theorem mem_cls {α r a z : V} : z ∈ˢ cls α r a ↔ z ∈ˢ α ∧ EqvC (QRel α r) a z := mem_sep

theorem cls_eq {α r a b : V} (h : EqvC (QRel α r) a b) : cls α r a = cls α r b :=
  Subset.antisymm (fun _ hz => mem_cls.mpr ⟨(mem_cls.mp hz).1, .trans (.symm h) (mem_cls.mp hz).2⟩)
    (fun _ hz => mem_cls.mpr ⟨(mem_cls.mp hz).1, .trans h (mem_cls.mp hz).2⟩)

theorem mem_cls_self {α r a : V} (ha : a ∈ˢ α) : a ∈ˢ cls α r a := mem_cls.mpr ⟨ha, .refl⟩

noncomputable def quotSet (u : Nat) (α r : V) : V := if u = 0 then α else image (cls α r) α
noncomputable def mkSet (u : Nat) (α r a : V) : V := if u = 0 then a else cls α r a
noncomputable def liftSet (u : Nat) (f q : V) : V := if u = 0 then app f q else app f (eps q)

theorem mkSet_mem {u : Nat} {α r a : V} (ha : a ∈ˢ α) : mkSet u α r a ∈ˢ quotSet u α r := by
  unfold mkSet quotSet; split
  · exact ha
  · exact mem_image.mpr ⟨a, ha, rfl⟩

theorem quotSet_cases {u : Nat} {α r q : V} (hq : q ∈ˢ quotSet u α r) :
    ∃ a, a ∈ˢ α ∧ q = mkSet u α r a := by
  unfold mkSet quotSet at *; split at hq
  · rename_i h; exact ⟨q, hq, by rw [ite_eq_left h]⟩
  · rename_i h; obtain ⟨a, ha, rfl⟩ := mem_image.mp hq; exact ⟨a, ha, by rw [ite_eq_right h]⟩

theorem quotSet_mem_univ {u : Nat} {α r : V} (hα : α ∈ˢ univ u) : quotSet u α r ∈ˢ univ u := by
  unfold quotSet; split
  · exact hα
  · rename_i hu
    have hU := univ_isTGUniverse (V := V) hu
    exact hU.image_mem hα fun a _ => hU.mem_of_subset_mem hα sep_subset

theorem eq_pt_of_cpi_prop {A f : V} {B : V → V} (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ 0 : V))
    (hf : f ∈ˢ cpi A B) : f = pt := by
  obtain ⟨g, hg, rfl⟩ := mem_cpi.mp hf
  unfold collapse
  rw [ite_eq_left fun x hx => mem_univ_zero (hB x hx) (app_mem_of_mem_piSet hg hx)]

theorem pt_mem_of_mem_prop {T x : V} (hT : T ∈ˢ (univ 0 : V)) (hx : x ∈ˢ T) : (pt : V) ∈ˢ T :=
  mem_univ_zero hT hx ▸ hx

theorem truthVal_mem_univ0 (p : Prop) : (truthVal p : V) ∈ˢ (univ 0 : V) := by
  rw [univ_zero]; exact truthVal_mem_univZero p

/-! ## The interpretation -/

noncomputable def M0 : CInterp V := fun _ _ => pt

def quotTel : List VExpr := [.sort (.param 0), relTy]
def quotMkTel : List VExpr := [.sort (.param 0), relTy, .bvar 1]
def quotLiftTel : List VExpr :=
  [.sort (.param 0), relTy, .sort (.param 1), .forallE (.bvar 2) (.bvar 1), cTy,
   .app (.app (.const `Quot [.param 0]) (.bvar 4)) (.bvar 3)]
def quotIndTel : List VExpr :=
  [.sort (.param 0), relTy,
   .forallE (.app (.app (.const `Quot [.param 0]) (.bvar 1)) (.bvar 0)) (.sort .zero),
   .forallE (.bvar 2) (.app (.bvar 1)
     (.app (.app (.app (.const `Quot.mk [.param 0]) (.bvar 3)) (.bvar 2)) (.bvar 0))),
   .app (.app (.const `Quot [.param 0]) (.bvar 3)) (.bvar 2)]

theorem quot_ty : quotConst.type = forallTel quotTel (.sort (.param 0)) := rfl
theorem quotMk_ty : quotMkConst.type = forallTel quotMkTel
    (.app (.app (.const `Quot [.param 0]) (.bvar 2)) (.bvar 1)) := rfl
theorem quotLift_ty : quotLiftConst.type = forallTel quotLiftTel (.bvar 3) := rfl
theorem quotInd_ty : quotIndConst.type = forallTel quotIndTel (.app (.bvar 2) (.bvar 0)) := rfl

noncomputable def stage1 : CInterp V := fun c ls =>
  if c = `Eq then lamTel M0 ls Eq_tel (fun ρ => truthVal (ρ.getD 1 pt = ρ.getD 0 pt)) []
  else if c = `Iff then lamTel M0 ls Iff_tel (fun ρ =>
    truthVal ((pt : V) ∈ˢ cpi (ρ.getD 1 pt) (fun _ => ρ.getD 0 pt) ∧
      (pt : V) ∈ˢ cpi (ρ.getD 0 pt) (fun _ => ρ.getD 1 pt))) []
  else if c = `Nonempty then lamTel M0 ls Nonempty_tel (fun ρ =>
      truthVal (∃ x, x ∈ˢ ρ.getD 0 pt)) []
  else if c = `Quot then lamTel M0 ls quotTel
    (fun ρ => quotSet (ls.getD 0 0) (ρ.getD 1 pt) (ρ.getD 0 pt)) []
  else if c = `Quot.mk then lamTel M0 ls quotMkTel
    (fun ρ => mkSet (ls.getD 0 0) (ρ.getD 2 pt) (ρ.getD 1 pt) (ρ.getD 0 pt)) []
  else pt

noncomputable def coreM : CInterp V := fun c ls =>
  if c = `Eq.rec then lamTel stage1 ls Eq_rec_tel (fun ρ => ρ.getD 2 pt) []
  else if c = `Iff.rec then lamTel stage1 ls Iff_rec_tel (fun ρ => app (app (ρ.getD 1 pt) pt) pt) []
  else if c = `Classical.choice then lamTel stage1 ls Classical_choice_tel
    (fun ρ => eps (ρ.getD 1 pt)) []
  else if c = `Quot.lift then lamTel stage1 ls quotLiftTel
    (fun ρ => liftSet (ls.getD 0 0) (ρ.getD 2 pt) (ρ.getD 0 pt)) []
  else stage1 c ls

theorem coreM_stage1 {c : Name} (h1 : c ≠ `Eq.rec) (h2 : c ≠ `Iff.rec)
    (h3 : c ≠ `Classical.choice) (h4 : c ≠ `Quot.lift) : coreM (V := V) c = stage1 c := by
  funext ls; unfold coreM; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]

abbrev S1 (c : Name) : Prop := c ≠ `Eq.rec ∧ c ≠ `Iff.rec ∧ c ≠ `Classical.choice ∧ c ≠ `Quot.lift

theorem S1.eq {c : Name} (h : S1 c) : coreM (V := V) c = stage1 c :=
  coreM_stage1 h.1 h.2.1 h.2.2.1 h.2.2.2

theorem lamTel_s1 {ls : List Nat} {As : List VExpr} {body : List V → V} {ρ : List V}
    (h : ∀ A ∈ As, ConstsIn S1 A) :
    lamTel stage1 ls As body ρ = lamTel coreM ls As body ρ :=
  lamTel_congrM fun A hA => (h A hA).mono fun _ hc => (S1.eq hc).symm

theorem lamTel_m0 {ls : List Nat} {As : List VExpr} {body : List V → V} {ρ : List V}
    (h : ∀ A ∈ As, ConstsIn (fun _ => False) A) :
    lamTel M0 ls As body ρ = lamTel coreM ls As body ρ :=
  lamTel_congrM fun A hA => (h A hA).mono fun _ hc => hc.elim

/-! ## Stage-1 constants applied -/

section
variable {u : Nat}

theorem coreM_Eq (ls : List Nat) : coreM (V := V) `Eq ls =
    lamTel M0 ls Eq_tel (fun ρ => truthVal (ρ.getD 1 pt = ρ.getD 0 pt)) [] := by
  rw [S1.eq (by decide)]; unfold stage1; rw [ite_eq_left rfl]

theorem coreM_Iff (ls : List Nat) : coreM (V := V) `Iff ls = lamTel M0 ls Iff_tel (fun ρ =>
    truthVal ((pt : V) ∈ˢ cpi (ρ.getD 1 pt) (fun _ => ρ.getD 0 pt) ∧
      (pt : V) ∈ˢ cpi (ρ.getD 0 pt) (fun _ => ρ.getD 1 pt))) [] := by
  rw [S1.eq (by decide)]; unfold stage1; rw [ite_eq_right (by decide), ite_eq_left rfl]

theorem coreM_Nonempty (ls : List Nat) : coreM (V := V) `Nonempty ls =
    lamTel M0 ls Nonempty_tel (fun ρ => truthVal (∃ x, x ∈ˢ ρ.getD 0 pt)) [] := by
  rw [S1.eq (by decide)]; unfold stage1; rw [ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left rfl]

theorem coreM_Quot (ls : List Nat) : coreM (V := V) `Quot ls = lamTel M0 ls quotTel
    (fun ρ => quotSet (ls.getD 0 0) (ρ.getD 1 pt) (ρ.getD 0 pt)) [] := by
  rw [S1.eq (by decide)]; unfold stage1
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

theorem coreM_mk (ls : List Nat) : coreM (V := V) `Quot.mk ls = lamTel M0 ls quotMkTel
    (fun ρ => mkSet (ls.getD 0 0) (ρ.getD 2 pt) (ρ.getD 1 pt) (ρ.getD 0 pt)) [] := by
  rw [S1.eq (by decide)]; unfold stage1
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_left rfl]

theorem coreM_pt {c : Name} (h : S1 c) (h1 : c ≠ `Eq) (h2 : c ≠ `Iff) (h3 : c ≠ `Nonempty)
    (h4 : c ≠ `Quot) (h5 : c ≠ `Quot.mk) (ls : List Nat) : coreM (V := V) c ls = pt := by
  rw [S1.eq h]; unfold stage1; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
      ite_eq_right h4, ite_eq_right h5]

theorem app_Eq {α a b : V} (hα : α ∈ˢ univ u) (ha : a ∈ˢ α) (hb : b ∈ˢ α) :
    app (app (app (coreM `Eq [u]) α) a) b = truthVal (a = b) := by
  rw [coreM_Eq]
  have := apps_lamTel (M := M0) (ls := [u])
    (body := fun ρ => (truthVal (ρ.getD 1 pt = ρ.getD 0 pt) : V)) (As := Eq_tel) (ρ := [])
    (xs := [α, a, b]) (.cons (by simpa [interp, VLevel.eval] using hα)
      (.cons (by simpa [interp] using ha) (.cons (by simpa [interp] using hb) .nil)))
  simpa using this

theorem app_Iff {a b : V} (ha : a ∈ˢ (univ 0 : V)) (hb : b ∈ˢ (univ 0 : V)) :
    app (app (coreM `Iff []) a) b =
      truthVal ((pt : V) ∈ˢ cpi a (fun _ => b) ∧ (pt : V) ∈ˢ cpi b (fun _ => a)) := by
  rw [coreM_Iff]
  have := apps_lamTel (M := M0) (ls := []) (body := fun ρ =>
    (truthVal ((pt : V) ∈ˢ cpi (ρ.getD 1 pt) (fun _ => ρ.getD 0 pt) ∧
      (pt : V) ∈ˢ cpi (ρ.getD 0 pt) (fun _ => ρ.getD 1 pt)) : V)) (As := Iff_tel) (ρ := [])
    (xs := [a, b]) (.cons (by simpa [interp, VLevel.eval] using ha)
      (.cons (by simpa [interp, VLevel.eval] using hb) .nil))
  simpa using this

theorem app_Nonempty {α : V} (hα : α ∈ˢ univ u) :
    app (coreM `Nonempty [u]) α = truthVal (∃ x, x ∈ˢ α) := by
  rw [coreM_Nonempty]
  have := apps_lamTel (M := M0) (ls := [u])
    (body := fun ρ => (truthVal (∃ x, x ∈ˢ ρ.getD 0 pt) : V)) (As := Nonempty_tel) (ρ := [])
    (xs := [α]) (.cons (by simpa [interp, VLevel.eval] using hα) .nil)
  simpa using this

theorem app_Quot {α r : V} (hα : α ∈ˢ univ u) (hr : r ∈ˢ relSet α) :
    app (app (coreM `Quot [u]) α) r = quotSet u α r := by
  rw [coreM_Quot]
  have := apps_lamTel (M := M0) (ls := [u])
    (body := fun ρ => quotSet ([u].getD 0 0) (ρ.getD 1 pt) (ρ.getD 0 pt)) (As := quotTel)
    (ρ := []) (xs := [α, r]) (.cons (by simpa [interp, VLevel.eval] using hα)
      (.cons (by rw [interp_relTy]; exact hr) .nil))
  simpa using this

theorem app_mk {α r a : V} (hα : α ∈ˢ univ u) (hr : r ∈ˢ relSet α) (ha : a ∈ˢ α) :
    app (app (app (coreM `Quot.mk [u]) α) r) a = mkSet u α r a := by
  rw [coreM_mk]
  have := apps_lamTel (M := M0) (ls := [u])
    (body := fun ρ => mkSet ([u].getD 0 0) (ρ.getD 2 pt) (ρ.getD 1 pt) (ρ.getD 0 pt))
    (As := quotMkTel) (ρ := []) (xs := [α, r, a]) (.cons (by simpa [interp, VLevel.eval] using hα)
      (.cons (by rw [interp_relTy]; exact hr) (.cons (by simpa [interp] using ha) .nil)))
  simpa using this

end

/-! ## The constants inhabit their types -/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

syntax "vsimp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| vsimp $[[$xs,*]]? $[$loc]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| simp only [interp, VLevel.eval, List.map, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.append_nil, List.getD_cons_zero,
        List.getD_cons_succ, List.singleton_append, $xs,*] $[$loc]?)

theorem ls1 {ls : List Nat} (h : ls.length = 1) : ∃ u, ls = [u] := by
  match ls, h with | [u], _ => exact ⟨u, rfl⟩
theorem ls2 {ls : List Nat} (h : ls.length = 2) : ∃ u v, ls = [u, v] := by
  match ls, h with | [u, v], _ => exact ⟨u, v, rfl⟩
theorem ls0 {ls : List Nat} (h : ls.length = 0) : ls = [] := List.eq_nil_of_length_eq_zero h

theorem mem_Eq (ls : List Nat) (ρ : List V) : coreM `Eq ls ∈ˢ interp coreM ls Eq_ty ρ := by
  rw [interp_closed coreM ls (by simp [Eq_ty, VExpr.ClosedN]) ρ, Eq_ty_eq, coreM_Eq,
    lamTel_m0 (by simp [Eq_tel, ConstsIn])]
  refine lamTel_mem fun xs _ => ?_
  simp only [Eq_res, interp, VLevel.eval]; exact truthVal_mem_univ0 _

theorem mem_Iff (ls : List Nat) (ρ : List V) : coreM `Iff ls ∈ˢ interp coreM ls Iff_ty ρ := by
  rw [interp_closed coreM ls (by simp [Iff_ty, VExpr.ClosedN]) ρ, Iff_ty_eq, coreM_Iff,
    lamTel_m0 (by simp [Iff_tel, ConstsIn])]
  refine lamTel_mem fun xs _ => ?_
  simp only [Iff_res, interp, VLevel.eval]; exact truthVal_mem_univ0 _

theorem mem_Nonempty (ls : List Nat) (ρ : List V) :
    coreM `Nonempty ls ∈ˢ interp coreM ls Nonempty_ty ρ := by
  rw [interp_closed coreM ls (by simp [Nonempty_ty, VExpr.ClosedN]) ρ, Nonempty_ty_eq,
    coreM_Nonempty, lamTel_m0 (by simp [Nonempty_tel, ConstsIn])]
  refine lamTel_mem fun xs _ => ?_
  simp only [Nonempty_res, interp, VLevel.eval]; exact truthVal_mem_univ0 _

theorem mem_Quot (ls : List Nat) (ρ : List V) :
    coreM `Quot ls ∈ˢ interp coreM ls quotConst.type ρ := by
  rw [interp_closed coreM ls (by simp [quot_ty, quotTel, relTy, forallTel, VExpr.ClosedN]) ρ,
    quot_ty, coreM_Quot, lamTel_m0 (by simp [quotTel, relTy, ConstsIn])]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨α, _, rfl, hα, r, _, rfl, -, rfl⟩ := by
    simpa only [quotTel, Ext_cons_iff, Ext_nil_iff] using hxs
  simp only [interp, VLevel.eval] at hα
  simpa [interp, VLevel.eval] using quotSet_mem_univ (r := r) hα

theorem mem_Eq_refl (ls : List Nat) (hl : ls.length = 1) (ρ : List V) :
    coreM `Eq.refl ls ∈ˢ interp coreM ls Eq_refl_ty ρ := by
  obtain ⟨u, rfl⟩ := ls1 hl
  rw [interp_closed coreM _ (by simp [Eq_refl_ty, VExpr.ClosedN]) ρ, Eq_refl_ty_eq,
    coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← lamTel_pt (M := coreM) (ls := [u]) (As := Eq_refl_tel) (ρ := [])]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨α, _, rfl, hα, a, _, rfl, ha, rfl⟩ := by
    simpa only [Eq_refl_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  vsimp at hα ha
  vsimp [Eq_refl_res]
  rw [app_Eq hα ha ha]; exact pt_mem_truthVal rfl

theorem mem_Iff_intro (ls : List Nat) (hl : ls.length = 0) (ρ : List V) :
    coreM `Iff.intro ls ∈ˢ interp coreM ls Iff_intro_ty ρ := by
  obtain rfl := ls0 hl
  rw [interp_closed coreM _ (by simp [Iff_intro_ty, VExpr.ClosedN]) ρ, Iff_intro_ty_eq,
    coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← lamTel_pt (M := coreM) (ls := []) (As := Iff_intro_tel) (ρ := [])]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨a, _, rfl, ha, b, _, rfl, hb, mp, _, rfl, hmp, mpr, _, rfl, hmpr, rfl⟩ := by
    simpa only [Iff_intro_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  vsimp at ha hb hmp hmpr
  vsimp [Iff_intro_res]
  rw [app_Iff ha hb]
  refine pt_mem_truthVal ⟨?_, ?_⟩
  · rwa [← eq_pt_of_cpi_prop (fun _ _ => hb) hmp]
  · rwa [← eq_pt_of_cpi_prop (fun _ _ => ha) hmpr]

theorem mem_Nonempty_intro (ls : List Nat) (hl : ls.length = 1) (ρ : List V) :
    coreM `Nonempty.intro ls ∈ˢ interp coreM ls Nonempty_intro_ty ρ := by
  obtain ⟨u, rfl⟩ := ls1 hl
  rw [interp_closed coreM _ (by simp [Nonempty_intro_ty, VExpr.ClosedN]) ρ, Nonempty_intro_ty_eq,
    coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← lamTel_pt (M := coreM) (ls := [u]) (As := Nonempty_intro_tel) (ρ := [])]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨α, _, rfl, hα, a, _, rfl, ha, rfl⟩ := by
    simpa only [Nonempty_intro_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  vsimp at hα ha
  vsimp [Nonempty_intro_res]
  rw [app_Nonempty hα]; exact pt_mem_truthVal ⟨a, ha⟩

theorem mem_Quot_mk (ls : List Nat) (hl : ls.length = 1) (ρ : List V) :
    coreM `Quot.mk ls ∈ˢ interp coreM ls quotMkConst.type ρ := by
  obtain ⟨u, rfl⟩ := ls1 hl
  rw [interp_closed coreM _ (by simp [quotMk_ty, quotMkTel, relTy, forallTel, VExpr.ClosedN]) ρ,
    quotMk_ty, coreM_mk, lamTel_m0 (by simp [quotMkTel, relTy, ConstsIn])]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨α, _, rfl, hα, r, _, rfl, hr, a, _, rfl, ha, rfl⟩ := by
    simpa only [quotMkTel, Ext_cons_iff, Ext_nil_iff] using hxs
  rw [interp_relTy] at hr
  vsimp at hα ha
  vsimp
  rw [app_Quot hα hr]; exact mkSet_mem ha

theorem mem_Eq_rec (ls : List Nat) (hl : ls.length = 2) (ρ : List V) :
    coreM `Eq.rec ls ∈ˢ interp coreM ls Eq_rec_ty ρ := by
  obtain ⟨v, u, rfl⟩ := ls2 hl
  rw [interp_closed coreM _ (by simp [Eq_rec_ty, VExpr.ClosedN]) ρ, Eq_rec_ty_eq]
  unfold coreM; rw [ite_eq_left rfl, lamTel_s1 (by simp [Eq_rec_tel, ConstsIn]; decide)]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨α, _, rfl, hα, a, _, rfl, ha, mot, _, rfl, -, m, _, rfl, hm, b, _, rfl, hb,
    t, _, rfl, ht, rfl⟩ := by simpa only [Eq_rec_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  vsimp at hα ha hm hb ht
  rw [app_Eq hα ha hb] at ht
  rw [coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    app_pt, app_pt] at hm
  obtain rfl := of_mem_truthVal ht
  obtain rfl := eq_pt_of_mem_truthVal ht
  vsimp [Eq_rec_res]; exact hm

theorem mem_Iff_rec (ls : List Nat) (hl : ls.length = 1) (ρ : List V) :
    coreM `Iff.rec ls ∈ˢ interp coreM ls Iff_rec_ty ρ := by
  obtain ⟨v, rfl⟩ := ls1 hl
  rw [interp_closed coreM _ (by simp [Iff_rec_ty, VExpr.ClosedN]) ρ, Iff_rec_ty_eq]
  unfold coreM; rw [ite_eq_right (by decide), ite_eq_left rfl,
      lamTel_s1 (by simp [Iff_rec_tel, ConstsIn]; decide)]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨a, _, rfl, ha, b, _, rfl, hb, mot, _, rfl, -, intro, _, rfl, hi, t, _, rfl, ht, rfl⟩ := by
    simpa only [Iff_rec_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  vsimp at ha hb hi ht
  rw [app_Iff ha hb] at ht
  obtain ⟨h1, h2⟩ := of_mem_truthVal ht
  obtain rfl := eq_pt_of_mem_truthVal ht
  have h3 := app_mem_cpi hi h1
  have := app_mem_cpi h3 h2
  rw [coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    app_pt, app_pt, app_pt, app_pt] at this
  vsimp [Iff_rec_res]; exact this

theorem mem_Nonempty_rec (ls : List Nat) (hl : ls.length = 1) (ρ : List V) :
    coreM `Nonempty.rec ls ∈ˢ interp coreM ls Nonempty_rec_ty ρ := by
  obtain ⟨u, rfl⟩ := ls1 hl
  rw [interp_closed coreM _ (by simp [Nonempty_rec_ty, VExpr.ClosedN]) ρ, Nonempty_rec_ty_eq,
    coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← lamTel_pt (M := coreM) (ls := [u]) (As := Nonempty_rec_tel) (ρ := [])]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨α, _, rfl, hα, mot, _, rfl, hmot, intro, _, rfl, hi, t, _, rfl, ht, rfl⟩ := by
    simpa only [Nonempty_rec_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  vsimp at hα hmot hi ht
  rw [app_Nonempty hα] at ht hmot
  obtain ⟨x, hx⟩ := of_mem_truthVal ht
  obtain rfl := eq_pt_of_mem_truthVal ht
  have h1 := app_mem_cpi hi hx
  rw [coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    app_pt, app_pt] at h1
  have h2 := app_mem_cpi hmot (pt_mem_truthVal ⟨x, hx⟩)
  vsimp [Nonempty_rec_res]
  exact pt_mem_of_mem_prop h2 h1

theorem mem_propext (ls : List Nat) (hl : ls.length = 0) (ρ : List V) :
    coreM `propext ls ∈ˢ interp coreM ls propext_ty ρ := by
  obtain rfl := ls0 hl
  rw [interp_closed coreM _ (by simp [propext_ty, VExpr.ClosedN]) ρ, propext_ty_eq,
    coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← lamTel_pt (M := coreM) (ls := []) (As := propext_tel) (ρ := [])]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨a, _, rfl, ha, b, _, rfl, hb, h, _, rfl, hh, rfl⟩ := by
    simpa only [propext_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  vsimp at ha hb hh
  rw [app_Iff ha hb] at hh
  obtain ⟨h1, h2⟩ := of_mem_truthVal hh
  vsimp [propext_res]
  rw [app_Eq (u := 1) (univ_mem_univ 0) ha hb]
  refine pt_mem_truthVal (Subset.antisymm (fun x hx => ?_) (fun x hx => ?_))
  · have := app_mem_cpi h1 hx; rw [app_pt] at this
    rwa [mem_univ_zero ha hx]
  · have := app_mem_cpi h2 hx; rw [app_pt] at this
    rwa [mem_univ_zero hb hx]

theorem mem_choice (ls : List Nat) (hl : ls.length = 1) (ρ : List V) :
    coreM `Classical.choice ls ∈ˢ interp coreM ls Classical_choice_ty ρ := by
  obtain ⟨u, rfl⟩ := ls1 hl
  rw [interp_closed coreM _ (by simp [Classical_choice_ty, VExpr.ClosedN]) ρ,
    Classical_choice_ty_eq]
  unfold coreM
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl,
    lamTel_s1 (by simp [Classical_choice_tel, ConstsIn]; decide)]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨α, _, rfl, hα, h, _, rfl, hh, rfl⟩ := by
    simpa only [Classical_choice_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  vsimp at hα hh
  rw [app_Nonempty hα] at hh
  obtain ⟨x, hx⟩ := of_mem_truthVal hh
  vsimp [Classical_choice_res]; exact eps_mem hx

theorem app_rel_prop {α r a b : V} (hr : r ∈ˢ relSet α) (ha : a ∈ˢ α) (hb : b ∈ˢ α) :
    app (app r a) b ∈ˢ (univ 0 : V) := by
  have h1 := app_mem_cpi hr ha
  exact app_mem_cpi h1 hb

theorem mem_Quot_lift (ls : List Nat) (hl : ls.length = 2) (ρ : List V) :
    coreM `Quot.lift ls ∈ˢ interp coreM ls quotLiftConst.type ρ := by
  obtain ⟨u, v, rfl⟩ := ls2 hl
  rw [interp_closed coreM _ (by simp [quotLift_ty, quotLiftTel, relTy, cTy, forallTel,
    VExpr.ClosedN]) ρ, quotLift_ty]
  unfold coreM
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl,
    lamTel_s1 (by simp [quotLiftTel, relTy, cTy, ConstsIn]; decide)]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨α, _, rfl, hα, r, _, rfl, hr, β, _, rfl, hβ, f, _, rfl, hf, c, _, rfl, -,
    q, _, rfl, hq, rfl⟩ := by simpa only [quotLiftTel, Ext_cons_iff, Ext_nil_iff] using hxs
  rw [interp_relTy] at hr
  vsimp at hα hβ hf hq
  rw [app_Quot hα hr] at hq
  vsimp
  obtain ⟨a, ha, rfl⟩ := quotSet_cases hq
  unfold liftSet mkSet; split
  · exact app_mem_cpi hf ha
  · exact app_mem_cpi hf (mem_cls.mp (eps_mem (mem_cls_self (r := r) ha))).1

theorem mem_Quot_ind (ls : List Nat) (hl : ls.length = 1) (ρ : List V) :
    coreM `Quot.ind ls ∈ˢ interp coreM ls quotIndConst.type ρ := by
  obtain ⟨u, rfl⟩ := ls1 hl
  rw [interp_closed coreM _ (by simp [quotInd_ty, quotIndTel, relTy, forallTel,
    VExpr.ClosedN]) ρ, quotInd_ty,
    coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← lamTel_pt (M := coreM) (ls := [u]) (As := quotIndTel) (ρ := [])]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨α, _, rfl, hα, r, _, rfl, hr, mot, _, rfl, hmot, h, _, rfl, hh, q, _, rfl, hq, rfl⟩ := by
    simpa only [quotIndTel, Ext_cons_iff, Ext_nil_iff] using hxs
  rw [interp_relTy] at hr
  vsimp at hα hmot hh hq
  rw [app_Quot hα hr] at hq hmot
  vsimp
  obtain ⟨a, ha, rfl⟩ := quotSet_cases hq
  have h1 := app_mem_cpi hh ha
  rw [app_mk hα hr ha] at h1
  exact pt_mem_of_mem_prop (app_mem_cpi hmot hq) h1

theorem mem_Quot_sound (ls : List Nat) (hl : ls.length = 1) (ρ : List V) :
    coreM `Quot.sound ls ∈ˢ interp coreM ls Quot_sound_ty ρ := by
  obtain ⟨u, rfl⟩ := ls1 hl
  rw [interp_closed coreM _ (by simp [Quot_sound_ty, VExpr.ClosedN]) ρ, Quot_sound_ty_eq,
    coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← lamTel_pt (M := coreM) (ls := [u]) (As := Quot_sound_tel) (ρ := [])]
  refine lamTel_mem fun xs hxs => ?_
  obtain ⟨α, _, rfl, hα, r, _, rfl, hr, a, _, rfl, ha, b, _, rfl, hb, h, _, rfl, hh, rfl⟩ := by
    simpa only [Quot_sound_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  vsimp at hα hr ha hb hh
  have hr' : r ∈ˢ relSet α := by simpa [relSet] using hr
  vsimp [Quot_sound_res]
  rw [app_Quot hα hr', app_mk hα hr' ha, app_mk hα hr' hb,
    app_Eq (quotSet_mem_univ hα) (mkSet_mem ha) (mkSet_mem hb)]
  refine pt_mem_truthVal ?_
  unfold mkSet; split
  · rename_i hu; subst hu
    exact (mem_univ_zero hα ha).trans (mem_univ_zero hα hb).symm
  · exact cls_eq (.rel ⟨ha, hb, pt_mem_of_mem_prop (app_rel_prop hr' ha hb) hh⟩)

/-! ## The iota rules -/

theorem coreM_Eq_rec (ls : List Nat) : coreM (V := V) `Eq.rec ls =
    lamTel coreM ls Eq_rec_tel (fun ρ => ρ.getD 2 pt) [] := by
  have : coreM (V := V) `Eq.rec ls = lamTel stage1 ls Eq_rec_tel (fun ρ => ρ.getD 2 pt) [] := by
    unfold coreM; rw [ite_eq_left rfl]
  rw [this, lamTel_s1 (by simp [Eq_rec_tel, ConstsIn]; decide)]

theorem coreM_Iff_rec (ls : List Nat) : coreM (V := V) `Iff.rec ls =
    lamTel coreM ls Iff_rec_tel (fun ρ => app (app (ρ.getD 1 pt) pt) pt) [] := by
  have : coreM (V := V) `Iff.rec ls =
      lamTel stage1 ls Iff_rec_tel (fun ρ => app (app (ρ.getD 1 pt) pt) pt) [] := by
    unfold coreM; rw [ite_eq_right (by decide), ite_eq_left rfl]
  rw [this, lamTel_s1 (by simp [Iff_rec_tel, ConstsIn]; decide)]

theorem coreM_lift (ls : List Nat) : coreM (V := V) `Quot.lift ls =
    lamTel coreM ls quotLiftTel (fun ρ => liftSet (ls.getD 0 0) (ρ.getD 2 pt)
        (ρ.getD 0 pt)) [] := by
  have : coreM (V := V) `Quot.lift ls = lamTel stage1 ls quotLiftTel
      (fun ρ => liftSet (ls.getD 0 0) (ρ.getD 2 pt) (ρ.getD 0 pt)) [] := by
    unfold coreM; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_left rfl]
  rw [this, lamTel_s1 (by simp [quotLiftTel, relTy, cTy, ConstsIn]; decide)]

theorem iota_of {ls : List Nat} {df : VDefEq} {tel : List VExpr} {lb rb res : VExpr}
    (hdf : df.lhs = lamTelE tel lb ∧ df.rhs = lamTelE tel rb ∧ df.type = forallTel tel res)
    (hc : df.lhs.ClosedN ∧ df.rhs.ClosedN ∧ df.type.ClosedN)
    (key : ∀ xs : List V, Ext (coreM (V := V)) ls tel [] xs →
      interp coreM ls lb (xs.reverse ++ []) = interp coreM ls rb (xs.reverse ++ []) ∧
      interp coreM ls rb (xs.reverse ++ []) ∈ˢ interp coreM ls res (xs.reverse ++ []))
    (ρ : List V) :
    interp coreM ls df.lhs ρ = interp coreM ls df.rhs ρ ∧
    interp coreM ls df.lhs ρ ∈ˢ interp coreM ls df.type ρ := by
  rw [interp_closed coreM ls hc.1 ρ, interp_closed coreM ls hc.2.1 ρ,
    interp_closed coreM ls hc.2.2 ρ, hdf.1, hdf.2.1, hdf.2.2, interp_lamTelE, interp_lamTelE]
  exact ⟨lamTel_congr fun xs h => (key xs h).1,
    lamTel_mem fun xs h => by rw [(key xs h).1]; exact (key xs h).2⟩

theorem iota_Eq (ls : List Nat) (hl : ls.length = 2) (ρ : List V) :
    interp coreM ls Eq_rec_iota0.lhs ρ = interp coreM ls Eq_rec_iota0.rhs ρ ∧
    interp coreM ls Eq_rec_iota0.lhs ρ ∈ˢ interp coreM ls Eq_rec_iota0.type ρ := by
  obtain ⟨v, u, rfl⟩ := ls2 hl
  refine iota_of Eq_rec_iota0_eq (by simp [Eq_rec_iota0, VExpr.ClosedN]) (fun xs hxs => ?_) ρ
  obtain ⟨α, _, rfl, hα, a, _, rfl, ha, mot, _, rfl, hmot, m, _, rfl, hm, rfl⟩ := by
    simpa only [Eq_rec_iota0_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  have hExt : Ext coreM [v, u] Eq_rec_tel [] [α, a, mot, m, a, pt] := by
    simp only [Eq_rec_tel, Ext_cons_iff, Ext_nil_iff]
    refine ⟨_, _, rfl, hα, _, _, rfl, ha, _, _, rfl, hmot, _, _, rfl, hm, _, _, rfl, ?_, _, _, rfl,
      ?_, rfl⟩
    · vsimp at ha ⊢; exact ha
    · vsimp at hα ha ⊢; rw [app_Eq hα ha ha]; exact pt_mem_truthVal rfl
  have hap := apps_lamTel (body := fun ρ => ρ.getD 2 pt) hExt
  vsimp at hα ha hm
  rw [coreM_pt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    app_pt, app_pt] at hm
  vsimp [Eq_rec_iota0_lhsb, Eq_rec_iota0_rhsb, Eq_rec_iota0_res]
  rw [coreM_Eq_rec, coreM_pt (c := `Eq.refl) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  simp only [app_pt]
  simp only [List.foldl, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.append_nil, List.getD_cons_zero, List.getD_cons_succ] at hap
  rw [hap]; exact ⟨rfl, hm⟩

theorem iota_Iff (ls : List Nat) (hl : ls.length = 1) (ρ : List V) :
    interp coreM ls Iff_rec_iota0.lhs ρ = interp coreM ls Iff_rec_iota0.rhs ρ ∧
    interp coreM ls Iff_rec_iota0.lhs ρ ∈ˢ interp coreM ls Iff_rec_iota0.type ρ := by
  obtain ⟨v, rfl⟩ := ls1 hl
  refine iota_of Iff_rec_iota0_eq (by simp [Iff_rec_iota0, VExpr.ClosedN]) (fun xs hxs => ?_) ρ
  obtain ⟨a, _, rfl, ha, b, _, rfl, hb, mot, _, rfl, hmot, intro, _, rfl, hi, mp, _, rfl, hmp,
    mpr, _, rfl, hmpr, rfl⟩ := by
    simpa only [Iff_rec_iota0_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  have ha1 := ha; have hb1 := hb
  vsimp at ha1 hb1 hmp hmpr
  have e1 := eq_pt_of_cpi_prop (fun _ _ => hb1) hmp
  have e2 := eq_pt_of_cpi_prop (fun _ _ => ha1) hmpr
  subst e1 e2
  have hExt : Ext coreM [v] Iff_rec_tel [] [a, b, mot, intro, pt] := by
    simp only [Iff_rec_tel, Ext_cons_iff, Ext_nil_iff]
    refine ⟨_, _, rfl, ha, _, _, rfl, hb, _, _, rfl, hmot, _, _, rfl, hi, _, _, rfl, ?_, rfl⟩
    vsimp; rw [app_Iff ha1 hb1]; exact pt_mem_truthVal ⟨hmp, hmpr⟩
  have hap := apps_lamTel (body := fun ρ => app (app (ρ.getD 1 pt) pt) pt) hExt
  vsimp at hi
  have h3 := app_mem_cpi hi hmp
  have h4 := app_mem_cpi h3 hmpr
  rw [coreM_pt (c := `Iff.intro) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)] at h4
  simp only [app_pt] at h4
  vsimp [Iff_rec_iota0_lhsb, Iff_rec_iota0_rhsb, Iff_rec_iota0_res]
  rw [coreM_Iff_rec, coreM_pt (c := `Iff.intro) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  simp only [app_pt]
  simp only [List.foldl, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.append_nil, List.getD_cons_zero, List.getD_cons_succ] at hap
  rw [hap]; exact ⟨rfl, h4⟩

theorem iota_Nonempty (ls : List Nat) (hl : ls.length = 1) (ρ : List V) :
    interp coreM ls Nonempty_rec_iota0.lhs ρ = interp coreM ls Nonempty_rec_iota0.rhs ρ ∧
    interp coreM ls Nonempty_rec_iota0.lhs ρ ∈ˢ interp coreM ls Nonempty_rec_iota0.type ρ := by
  obtain ⟨u, rfl⟩ := ls1 hl
  refine iota_of Nonempty_rec_iota0_eq (by simp [Nonempty_rec_iota0, VExpr.ClosedN])
    (fun xs hxs => ?_) ρ
  obtain ⟨α, _, rfl, hα, mot, _, rfl, hmot, intro, _, rfl, hi, x, _, rfl, hx, rfl⟩ := by
    simpa only [Nonempty_rec_iota0_tel, Ext_cons_iff, Ext_nil_iff] using hxs
  vsimp at hα hmot hi hx
  rw [app_Nonempty hα] at hmot
  have h1 := app_mem_cpi hi hx
  rw [coreM_pt (c := `Nonempty.intro) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)] at h1
  simp only [app_pt] at h1
  have hP := app_mem_cpi hmot (pt_mem_truthVal ⟨x, hx⟩)
  have e := mem_univ_zero hP h1
  vsimp [Nonempty_rec_iota0_lhsb, Nonempty_rec_iota0_rhsb, Nonempty_rec_iota0_res]
  rw [coreM_pt (c := `Nonempty.rec) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    coreM_pt (c := `Nonempty.intro) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
  simp only [app_pt]
  rw [e]
  exact ⟨rfl, e ▸ h1⟩

def quotIotaTel : List VExpr :=
  [.sort (.param 0), relTy, .sort (.param 1), .forallE (.bvar 2) (.bvar 1), cTy, .bvar 4]
def quotIotaL : VExpr :=
  .app (.app (.app (.app (.app (.app (.const `Quot.lift [.param 0, .param 1]) (.bvar 5))
    (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1))
    (.app (.app (.app (.const `Quot.mk [.param 0]) (.bvar 5)) (.bvar 4)) (.bvar 0))

theorem quotDefEq_eq : quotDefEq.lhs = lamTelE quotIotaTel quotIotaL ∧
    quotDefEq.rhs = lamTelE quotIotaTel (.app (.bvar 2) (.bvar 0)) ∧
    quotDefEq.type = forallTel quotIotaTel (.bvar 3) := by
  rw [defeq_eq]; exact ⟨rfl, rfl, rfl⟩

theorem respects {u v : Nat} {α r β f c : V} (hβ : β ∈ˢ univ v) (hf : f ∈ˢ cpi α fun _ => β)
    (hc : c ∈ˢ interp coreM [u, v] cTy [f, β, r, α]) :
    ∀ {a b}, EqvC (QRel α r) a b → app f a = app f b := by
  intro a b h
  induction h with
  | rel h =>
    obtain ⟨ha, hb, hab⟩ := h
    vsimp [cTy] at hc
    have h1 := app_mem_cpi hc ha
    have h2 := app_mem_cpi h1 hb
    have h3 := app_mem_cpi h2 hab
    rw [app_Eq hβ (app_mem_cpi hf ha) (app_mem_cpi hf hb)] at h3
    exact of_mem_truthVal h3
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem iota_Quot (ls : List Nat) (hl : ls.length = 2) (ρ : List V) :
    interp coreM ls quotDefEq.lhs ρ = interp coreM ls quotDefEq.rhs ρ ∧
    interp coreM ls quotDefEq.lhs ρ ∈ˢ interp coreM ls quotDefEq.type ρ := by
  obtain ⟨u, v, rfl⟩ := ls2 hl
  refine iota_of quotDefEq_eq (by rw [defeq_eq]; simp [relTy, cTy, VExpr.ClosedN])
    (fun xs hxs => ?_) ρ
  obtain ⟨α, _, rfl, hα, r, _, rfl, hr, β, _, rfl, hβ, f, _, rfl, hf, c, _, rfl, hc,
    a, _, rfl, ha, rfl⟩ := by simpa only [quotIotaTel, Ext_cons_iff, Ext_nil_iff] using hxs
  have hα1 := hα; have hβ1 := hβ; have hf1 := hf; have ha1 := ha
  rw [interp_relTy] at hr
  vsimp at hα1 hβ1 hf1 ha1
  have hExt : Ext coreM [u, v] quotLiftTel [] [α, r, β, f, c, mkSet u α r a] := by
    simp only [quotLiftTel, Ext_cons_iff, Ext_nil_iff]
    refine ⟨_, _, rfl, hα, _, _, rfl, by rw [interp_relTy]; exact hr, _, _, rfl, hβ, _, _, rfl, hf,
      _, _, rfl, hc, _, _, rfl, ?_, rfl⟩
    vsimp; rw [app_Quot hα1 hr]; exact mkSet_mem ha1
  have hap := apps_lamTel (body := fun ρ => liftSet ([u, v].getD 0 0) (ρ.getD 2 pt) (ρ.getD 0 pt))
    hExt
  simp only [List.foldl, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.append_nil, List.getD_cons_zero, List.getD_cons_succ] at hap
  vsimp [quotIotaL]
  rw [app_mk hα1 hr ha1, coreM_lift]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [hap]
  refine ⟨?_, app_mem_cpi hf1 ha1⟩
  unfold liftSet mkSet; split
  · rfl
  · exact (respects hβ1 hf1 hc (mem_cls.mp (eps_mem (mem_cls_self (r := r) ha1))).2).symm

/-! ## The core environment -/

def lookupC : List (Name × VConstant) → Name → Option VConstant
  | [], _ => none
  | (k, c) :: l, n => if n = k then some c else lookupC l n

theorem lookupC_mem : ∀ {l : List (Name × VConstant)} {n c}, lookupC l n = some c → (n, c) ∈ l
  | [], _, _, h => nomatch h
  | (k, c') :: l, n, c, h => by
    unfold lookupC at h; split at h
    · cases h; subst n; exact .head _
    · exact .tail _ (lookupC_mem h)

theorem lookupC_ne_none : ∀ {l : List (Name × VConstant)} {n}, n ∈ l.map Prod.fst →
    lookupC l n ≠ none
  | [], _, h => nomatch h
  | (k, c') :: l, n, h => by
    unfold lookupC; split
    · simp
    · rename_i hne
      exact lookupC_ne_none ((List.mem_cons.mp h).resolve_left hne)

def coreConsts : List (Name × VConstant) :=
  [(`Eq, Eq_c.toVConstant), (`Eq.refl, Eq_refl_c.toVConstant), (`Eq.rec, Eq_rec_c.toVConstant),
   (`Iff, Iff_c.toVConstant), (`Iff.intro, Iff_intro_c.toVConstant),
   (`Iff.rec, Iff_rec_c.toVConstant), (`Nonempty, Nonempty_c.toVConstant),
   (`Nonempty.intro, Nonempty_intro_c.toVConstant), (`Nonempty.rec, Nonempty_rec_c.toVConstant),
   (`propext, propext_c.toVConstant), (`Classical.choice, Classical_choice_c.toVConstant),
   (`Quot, quotConst), (`Quot.mk, quotMkConst), (`Quot.lift, quotLiftConst),
   (`Quot.ind, quotIndConst), (`Quot.sound, Quot_sound_c.toVConstant)]

def coreDefeqs : List VDefEq := [Eq_rec_iota0, Iff_rec_iota0, Nonempty_rec_iota0, quotDefEq]

/-- Lean's core logic: `Eq`, `Iff`, `Nonempty`, the quotient primitives and three axioms. -/
def coreEnv : VEnv where
  constants := lookupC coreConsts
  defeqs := (· ∈ coreDefeqs)

theorem coreM_model : IsModel (coreM (V := V)) coreEnv := by
  constructor
  · intro c ci h ls hl ρ
    have := lookupC_mem h
    simp only [coreConsts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at this
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact mem_Eq ls ρ
    · exact mem_Eq_refl ls hl ρ
    · exact mem_Eq_rec ls hl ρ
    · exact mem_Iff ls ρ
    · exact mem_Iff_intro ls hl ρ
    · exact mem_Iff_rec ls hl ρ
    · exact mem_Nonempty ls ρ
    · exact mem_Nonempty_intro ls hl ρ
    · exact mem_Nonempty_rec ls hl ρ
    · exact mem_propext ls hl ρ
    · exact mem_choice ls hl ρ
    · exact mem_Quot ls ρ
    · exact mem_Quot_mk ls hl ρ
    · exact mem_Quot_lift ls hl ρ
    · exact mem_Quot_ind ls hl ρ
    · exact mem_Quot_sound ls hl ρ
  · intro df h ls hl ρ
    simp only [coreEnv, coreDefeqs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact iota_Eq ls hl ρ
    · exact iota_Iff ls hl ρ
    · exact iota_Nonempty ls hl ρ
    · exact iota_Quot ls hl ρ

/-! ## The syntactic invariant -/

def cnames : VExpr → List Name
  | .bvar _ | .sort _ => []
  | .const c _ => [c]
  | .app f a | .lam f a | .forallE f a => cnames f ++ cnames a

theorem constsIn_of_cnames {P : Name → Prop} : ∀ {e : VExpr}, (∀ c ∈ cnames e, P c) → ConstsIn P e
  | .bvar _, _ | .sort _, _ => trivial
  | .const _ _, h => h _ (.head _)
  | .app .., h | .lam .., h | .forallE .., h =>
    ⟨constsIn_of_cnames fun c hc => h c (List.mem_append_left _ hc),
     constsIn_of_cnames fun c hc => h c (List.mem_append_right _ hc)⟩

theorem core_constsIn {e : VExpr} (h : ∀ c ∈ cnames e, c ∈ coreConsts.map Prod.fst) :
    ConstsIn (Dom coreEnv) e :=
  constsIn_of_cnames fun c hc => lookupC_ne_none (h c hc)

theorem coreEnv_good : Good coreEnv := by
  refine ⟨⟨fun {n ci} h => ?_, fun {df} h => ?_⟩, ⟨fun {n ci} h => ?_, fun {df} h => ?_⟩⟩
  · refine ⟨.zero, ?_, trivial⟩
    have := lookupC_mem h
    simp only [coreConsts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at this
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [VConstVal.toVConstant, Eq_c, Eq_ty, Eq_refl_c, Eq_refl_ty, Eq_rec_c, Eq_rec_ty, Iff_c,
      Iff_ty, Iff_intro_c, Iff_intro_ty, Iff_rec_c, Iff_rec_ty, Nonempty_c, Nonempty_ty,
      Nonempty_intro_c, Nonempty_intro_ty, Nonempty_rec_c, Nonempty_rec_ty, propext_c, propext_ty,
      Classical_choice_c, Classical_choice_ty, Quot_sound_c, Quot_sound_ty, quot_ty, quotMk_ty,
      quotLift_ty, quotInd_ty, quotTel, quotMkTel, quotLiftTel, quotIndTel, relTy, cTy, forallTel,
      VExpr.ClosedN]
  · simp only [coreEnv, coreDefeqs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · simp [Eq_rec_iota0, VExpr.ClosedN]
    · simp [Iff_rec_iota0, VExpr.ClosedN]
    · simp [Nonempty_rec_iota0, VExpr.ClosedN]
    · rw [defeq_eq]; simp [relTy, cTy, VExpr.ClosedN]
  · refine ⟨.zero, ?_, trivial⟩
    have := lookupC_mem h
    simp only [coreConsts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at this
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact core_constsIn (by decide)
  · simp only [coreEnv, coreDefeqs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;>
    exact ⟨⟨core_constsIn (by decide), core_constsIn (by decide)⟩, core_constsIn (by decide),
      core_constsIn (by decide)⟩

end Soulgem.Core
