import Soulgem.Model.Restore
import Soulgem.Model.BlockFinal

/-! # Nested blocks: the data of the restoration argument -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

theorem getElem_eq_getElem! {α : Type _} [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    l[i] = l[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

noncomputable abbrev carrierFn (M : CInterp V) (b : SBlock) : List Nat → List V → Nat → V :=
  fun ls ρp => carrier M ls b ρp

theorem _root_.Soulgem.BlockModel.Setting.not_name {M : CInterp V} {env env₁ : VEnv}
    {b : SBlock} (S : Setting M env env₁ b) {c : Name} (hc : Dom env c) : c ∉ b.names := by
  intro hm
  have h := S.hwt; rw [withTypes_eq] at h
  obtain ⟨hfr, _⟩ := addFold_spec h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  exact hc (hfr (t.name, _) (List.mem_map.mpr ⟨t, ht, rfl⟩))

structure CanonR (M : CInterp V) (env : VEnv) (r : RBlock) (MJ : CInterp V) (envJ envJ₁ : VEnv) :
    Prop where
  setting : Setting MJ envJ envJ₁ r.b
  le : envJ ≤ env
  agree : ∀ c, Dom envJ c → M c = MJ c
  slots : ∀ σ < r.b.ntypes, ∃ k, r.slotKey σ = some k ∧ k.ClosedN r.b.nparams ∧
    ConstsIn (Dom env) k ∧ (∃ c us as, k = appN (.const c us) as) ∧
    ∀ ls ρ, ls.length = r.b.uvars → Ext MJ ls r.b.params [] ρ →
      interp M ls k ρ.reverse = ρ.foldl app (M₁ MJ r.b (carrierFn MJ r.b) (r.b.types[σ]!).name ls)
  slotCtors : ∀ σ < r.b.ntypes, ∀ q (c : SCtor), (ctorsOf r.b σ)[q]? = some c → ∀ k,
    r.slotKey σ = some k → ∀ Ic Ils Ds, headArgs k = (.const Ic Ils, Ds) →
      Dom env (c.name.replacePrefix (r.b.types[σ]!).name Ic) ∧
      ∀ ls ρ, ls.length = r.b.uvars → Ext MJ ls r.b.params [] ρ →
        interp M ls (appN (.const (c.name.replacePrefix (r.b.types[σ]!).name Ic) Ils)
            Ds) ρ.reverse =
          ρ.foldl app (Setting.ctorVal r.b (Setting.Mc MJ r.b) ls q c)
  recs : r.tr.types = [] → 0 < r.b.ntypes → ∃ e₂ e₃, addFold envJ₁ (ctorConsts r.b) = some e₂ ∧
    addFold e₂ (recConsts r.b) = some e₃ ∧ Dom env (r.b.recName 0) ∧ M (r.b.recName 0) =
        M₃ MJ r.b (r.b.recName 0)

def auxAt (tr : Translated) (nuser g : Nat) : Option Aux :=
  if g < nuser then none else tr.aux[g - nuser]?

noncomputable def keyArgs (M : CInterp V) (ls : List Nat) (Ds : List VExpr)
    (ρp : List V) : List V :=
  (Ds.map (interp M ls · ρp)).reverse

theorem keyArgs_getD (M : CInterp V) (ls : List Nat) (Ds : List VExpr) (ρp : List V) {i : Nat}
    (hi : i < Ds.length) :
    (keyArgs M ls Ds ρp).getD i pt = interp M ls (Ds.reverse[i]!) ρp := by
  unfold keyArgs
  rw [← List.map_reverse, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hi)]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem
      (by simpa using hi : i < Ds.reverse.length)]

theorem keyArgs_length (M : CInterp V) (ls : List Nat) (Ds : List VExpr) (ρp : List V) :
    (keyArgs M ls Ds ρp).length = Ds.length := by simp [keyArgs]

/-! ## Terms equal up to equivalent levels (`EqL`) -/

theorem levels_eval {us vs : List VLevel} (h : List.Forall₂ (· ≈ ·) us vs) (ls : List Nat) :
    us.map (VLevel.eval ls) = vs.map (VLevel.eval ls) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, ih]; exact congrFun h ls ▸ rfl

theorem forall₂_append {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ l₁' l₂ l₂'}, List.Forall₂ R l₁ l₁' → List.Forall₂ R l₂ l₂' →
      List.Forall₂ R (l₁ ++ l₂) (l₁' ++ l₂')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (forall₂_append t h')

theorem forall₂_map {α β : Type _} {R : α → α → Prop} {S : β → β → Prop} {f g : α → β}
    (H : ∀ a b, R a b → S (f a) (g b)) :
    ∀ {l l'}, List.Forall₂ R l l' → List.Forall₂ S (l.map f) (l'.map g)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (H _ _ h) (forall₂_map H t)

theorem instL_appN (ls : List VLevel) : ∀ (f : VExpr) (as : List VExpr),
    (appN f as).instL ls = appN (f.instL ls) (as.map (·.instL ls))
  | _, [] => rfl
  | f, a :: as => instL_appN ls (.app f a) as

theorem subst_appN (g : Nat → VExpr) (k : Nat) : ∀ (f : VExpr) (as : List VExpr),
    subst g (appN f as) k = appN (subst g f k) (as.map (subst g · k))
  | _, [] => rfl
  | f, a :: as => subst_appN g k (.app f a) as

theorem atKey_appN_const (lv : List VLevel) (Ds : List VExpr) (k : Nat) (c : Name)
    (us : List VLevel) (as : List VExpr) :
    atKey lv Ds k (appN (.const c us) as) = appN (.const c (us.map (·.inst lv)))
      (as.map fun x => Spec.subst (argSubst Ds) (x.instL lv) k) := by
  unfold atKey; rw [instL_appN, subst_appN, List.map_map]; rfl

theorem replacePrefix_self : ∀ (n X : Lean.Name), n.replacePrefix n X = X
  | .anonymous, _ => rfl
  | .str p s, _ => by simp [Lean.Name.replacePrefix]
  | .num p i, _ => by simp [Lean.Name.replacePrefix]

theorem replacePrefix_swap (T A I : Lean.Name) : ∀ c : Lean.Name,
    (c.replacePrefix T A).replacePrefix A T = c →
    (c.replacePrefix T A).replacePrefix A I = c.replacePrefix T I
  | .anonymous, h => by
    by_cases hT : T = .anonymous
    · subst hT; simp only [Lean.Name.replacePrefix] at h ⊢; rw [replacePrefix_self]
    · have e : Lean.Name.anonymous.replacePrefix T A = .anonymous := by
        cases T <;> simp_all [Lean.Name.replacePrefix]
      rw [e] at h ⊢
      have hA : A ≠ .anonymous := fun hA => by
          subst hA; simp [Lean.Name.replacePrefix] at h; exact hT h
      cases A <;> cases T <;> simp_all [Lean.Name.replacePrefix]
  | .str p s, h => by
    by_cases hc : Lean.Name.str p s = T
    · subst hc; simp only [Lean.Name.replacePrefix, beq_self_eq_true, ite_true] at h ⊢
      rw [replacePrefix_self]
    · have e1 : (Lean.Name.str p s).replacePrefix T A = Lean.Name.str (p.replacePrefix T A) s := by
        simp [Lean.Name.replacePrefix, hc]
      have e2 : (Lean.Name.str p s).replacePrefix T I = Lean.Name.str (p.replacePrefix T I) s := by
        simp [Lean.Name.replacePrefix, hc]
      rw [e1] at h ⊢; rw [e2]
      by_cases hA : Lean.Name.str (p.replacePrefix T A) s = A
      · rw [hA, replacePrefix_self] at h; exact absurd h.symm hc
      · simp only [Lean.Name.replacePrefix, beq_iff_eq, hA, ite_false, Lean.Name.mkStr] at h ⊢
        injection h with h1
        rw [replacePrefix_swap T A I p h1]
  | .num p i, h => by
    by_cases hc : Lean.Name.num p i = T
    · subst hc; simp only [Lean.Name.replacePrefix, beq_self_eq_true, ite_true] at h ⊢
      rw [replacePrefix_self]
    · have e1 : (Lean.Name.num p i).replacePrefix T A = Lean.Name.num (p.replacePrefix T A) i := by
        simp [Lean.Name.replacePrefix, hc]
      have e2 : (Lean.Name.num p i).replacePrefix T I = Lean.Name.num (p.replacePrefix T I) i := by
        simp [Lean.Name.replacePrefix, hc]
      rw [e1] at h ⊢; rw [e2]
      by_cases hA : Lean.Name.num (p.replacePrefix T A) i = A
      · rw [hA, replacePrefix_self] at h; exact absurd h.symm hc
      · simp only [Lean.Name.replacePrefix, beq_iff_eq, hA, ite_false, Lean.Name.mkNum] at h ⊢
        injection h with h1
        rw [replacePrefix_swap T A I p h1]

theorem replacePrefix_same (T : Lean.Name) : ∀ n : Lean.Name, n.replacePrefix T T = n
  | .anonymous => by cases T <;> simp [Lean.Name.replacePrefix]
  | .str p s => by
    by_cases h : Lean.Name.str p s = T
    · subst h; simp [Lean.Name.replacePrefix]
    · simp [Lean.Name.replacePrefix, h, replacePrefix_same T p]
  | .num p i => by
    by_cases h : Lean.Name.num p i = T
    · subst h; simp [Lean.Name.replacePrefix]
    · simp [Lean.Name.replacePrefix, h, replacePrefix_same T p]

theorem closedN_ownKey (c : Name) (us : List VLevel) (n : Nat) :
    (appN (.const c us) (vars n 0 n)).ClosedN n :=
  closedN_appN_of trivial fun D hD => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hD
    simp only [List.mem_range] at hi
    simp only [var, VExpr.ClosedN]; omega

theorem closedN_appN_inv {k : Nat} : ∀ {f : VExpr} {as : List VExpr}, (appN f as).ClosedN k →
    f.ClosedN k ∧ ∀ a ∈ as, a.ClosedN k
  | _, [], h => ⟨h, nofun⟩
  | f, a :: as, h => by
    obtain ⟨⟨hf, ha⟩, has⟩ := closedN_appN_inv (f := .app f a) (as := as) h
    exact ⟨hf, fun x hx => (List.mem_cons.mp hx).elim (· ▸ ha) (has x)⟩

theorem closedN_subst {f : Nat → VExpr} {N n : Nat} (hf : ∀ i < N, (f i).ClosedN n) :
    ∀ {e : VExpr} {k : Nat}, e.ClosedN (k + N) → (Spec.subst f e k).ClosedN (k + n)
  | .bvar i, k, h => by
    simp only [Spec.subst]
    split
    · simp only [VExpr.ClosedN] at *; omega
    · rename_i hi
      have hi' : i - k < N := by simp only [VExpr.ClosedN] at h; omega
      have := (hf _ hi').liftN (n := k) (j := 0)
      rwa [Nat.add_comm] at this
  | .sort _, _, _ | .const _ _, _, _ => trivial
  | .app .., _, ⟨h1, h2⟩ => ⟨closedN_subst hf h1, closedN_subst hf h2⟩
  | .lam .., k, ⟨h1, h2⟩ | .forallE .., k, ⟨h1, h2⟩ => by
    refine ⟨closedN_subst hf h1, ?_⟩
    have := closedN_subst hf (k := k + 1) (by rwa [Nat.add_right_comm] at h2)
    rwa [Nat.add_right_comm] at this

theorem constsIn_subst {P : Name → Prop} {f : Nat → VExpr} (hf : ∀ i, ConstsIn P (f i)) :
    ∀ {e : VExpr} {k : Nat}, ConstsIn P e → ConstsIn P (Spec.subst f e k)
  | .bvar i, k, _ => by
    simp only [Spec.subst]; split
    · trivial
    · exact constsIn_liftN.mpr (hf _)
  | .sort _, _, _ => trivial
  | .const _ _, _, h => h
  | .app .., _, ⟨h1, h2⟩ | .lam .., _, ⟨h1, h2⟩ | .forallE .., _, ⟨h1, h2⟩ =>
    ⟨constsIn_subst hf h1, constsIn_subst hf h2⟩

theorem constsIn_argSubst {P : Name → Prop} {Ds : List VExpr}
    (h : ∀ D ∈ Ds, ConstsIn P D) (i : Nat) : ConstsIn P (argSubst Ds i) := by
  unfold argSubst; split
  · exact h _ (List.mem_reverse.mp (List.getElem_mem _))
  · trivial

theorem interp_ownKey {V : Type _} [SetTheory V] (M : CInterp V) (ls : List Nat) {c : Name}
    {u n : Nat} {ρ : List V} (hl : ls.length = u) (hρ : ρ.length = n) :
    interp M ls (appN (.const c (ownLevels u)) (vars n 0 n)) ρ.reverse = ρ.foldl app (M c ls) := by
  rw [interp_appN, interp_vars M ls hρ (by omega)]
  simp only [interp, List.drop_zero, List.take_of_length_le (Nat.le_of_eq hρ)]
  exact congrArg (List.foldl app · ρ) (congrArg (M c) (map_eval_params hl))

namespace EqL

theorem closedN : ∀ {e e' : VExpr} {k : Nat}, e.EqL e' → e'.ClosedN k → e.ClosedN k
  | .bvar _, .bvar _, _, h, hc => h ▸ hc
  | .sort _, .sort _, _, _, _ | .const _ _, .const _ _, _, _, _ => trivial
  | .app .., .app .., _, ⟨h1, h2⟩, ⟨c1, c2⟩ | .lam .., .lam .., _, ⟨h1, h2⟩, ⟨c1, c2⟩
  | .forallE .., .forallE .., _, ⟨h1, h2⟩, ⟨c1, c2⟩ => ⟨closedN h1 c1, closedN h2 c2⟩

theorem constsIn {P : Name → Prop} : ∀ {e e' : VExpr}, e.EqL e' → ConstsIn P e' → ConstsIn P e
  | .bvar _, .bvar _, _, _ | .sort _, .sort _, _, _ => trivial
  | .const _ _, .const _ _, ⟨h1, _⟩, hc => h1 ▸ hc
  | .app .., .app .., ⟨h1, h2⟩, ⟨c1, c2⟩ | .lam .., .lam .., ⟨h1, h2⟩, ⟨c1, c2⟩
  | .forallE .., .forallE .., ⟨h1, h2⟩, ⟨c1, c2⟩ => ⟨constsIn h1 c1, constsIn h2 c2⟩

theorem appN_congr : ∀ {f g : VExpr} {as Ds : List VExpr}, f.EqL g →
    List.Forall₂ VExpr.EqL as Ds → (appN f as).EqL (appN g Ds)
  | _, _, _, _, hf, .nil => hf
  | _, _, _, _, hf, .cons h t => appN_congr (f := .app _ _) (g := .app _ _) ⟨hf, h⟩ t

theorem appN_const_rev {c : Name} {us : List VLevel} : ∀ (l : List VExpr) {e : VExpr},
    e.EqL (appN (.const c us) l.reverse) →
    ∃ us' as', e = appN (.const c us') as' ∧ List.Forall₂ (· ≈ ·) us' us ∧
      List.Forall₂ VExpr.EqL as' l.reverse
  | [], e, h => by
    match e, h with
    | .const _ us', ⟨rfl, h2⟩ => exact ⟨us', [], rfl, h2, .nil⟩
  | x :: l, e, h => by
    simp only [List.reverse_cons, appN, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    match e, h with
    | .app f a, ⟨h1, h2⟩ =>
      obtain ⟨us', as', rfl, hu, ha⟩ := appN_const_rev l h1
      exact ⟨us', as' ++ [a], by
          simp [appN], hu, by rw [List.reverse_cons]; exact forall₂_append ha (.cons h2 .nil)⟩

theorem appN_const {c : Name} {us : List VLevel} {as : List VExpr} {e : VExpr}
    (h : e.EqL (appN (.const c us) as)) :
    ∃ us' as', e = appN (.const c us') as' ∧ List.Forall₂ (· ≈ ·) us' us ∧
      List.Forall₂ VExpr.EqL as' as := by
  have := appN_const_rev (c := c) (us := us) as.reverse (e := e); rw [List.reverse_reverse] at this
  exact this h

end EqL

theorem interp_EqL (M : CInterp V) (ls : List Nat) : ∀ {e e' : VExpr}, e.EqL e' → ∀ ρ,
    interp M ls e ρ = interp M ls e' ρ
  | .bvar _, .bvar _, h, _ => by subst h; rfl
  | .sort _, .sort _, h, _ => by simp only [interp, congrFun h ls]
  | .const _ _, .const _ _, ⟨h1, h2⟩, _ => by simp only [interp, h1, levels_eval h2]
  | .app .., .app .., ⟨h1, h2⟩, ρ => by simp only [interp, interp_EqL M ls h1, interp_EqL M ls h2]
  | .lam .., .lam .., ⟨h1, h2⟩, ρ | .forallE .., .forallE .., ⟨h1, h2⟩, ρ => by
    simp only [interp, interp_EqL M ls h1]; congr 1; funext x; exact interp_EqL M ls h2 _

theorem interp_atKey (M : CInterp V) (ls : List Nat) (lv : List VLevel) (Ds : List VExpr)
    (ρp : List V) {e : VExpr} {k : Nat} (hc : e.ClosedN (k + Ds.length)) (ys : List V)
    (hys : ys.length = k) :
    interp M ls (atKey lv Ds k e) (ys ++ ρp) =
      interp M (lv.map (VLevel.eval ls)) e (ys ++ keyArgs M ls Ds ρp) := by
  unfold atKey
  rw [interp_subst M ls _ _ k Ds.length ys ρp (keyArgs M ls Ds ρp) hc.instL hys
    (fun i hi => by
        rw [keyArgs_getD M ls Ds ρp hi, argSubst, dite_eq_left hi, getElem_eq_getElem!]),
    interp_instL]

theorem EqLTel.get {lv : List VLevel} {Ds : List VExpr} : ∀ {k : Nat} {as bs : List VExpr},
    EqLTel lv Ds k as bs → as.length = bs.length ∧
      ∀ l (h : l < as.length) (h' : l < bs.length), as[l].EqL (atKey lv Ds (k + l) bs[l])
  | _, [], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k, _ :: _, _ :: _, ⟨h0, t⟩ => by
    obtain ⟨hl, hg⟩ := EqLTel.get t
    refine ⟨by simp [hl], fun l h h' => ?_⟩
    cases l with
    | zero => simp only [List.getElem_cons_zero, Nat.add_zero]; exact h0
    | succ l =>
      have := hg l (by simpa using h) (by simpa using h'); rwa [Nat.add_assoc,
          Nat.add_comm 1] at this

/-! ## A family slot -/

def FamLink (rec : List RBlock) (tr : Translated) (nuser : Nat) (fams : List Fam) (a : Aux)
    (lv : List VLevel) (Ds : List VExpr) (r : RBlock) (m d : Nat) : Prop :=
  ∃ j, ∃ hj : j < fams.length, fams[j].lv = lv ∧ fams[j].Ds = Ds ∧ rec[fams[j].ri]? = some r ∧
    nuser ≤ d ∧ fams[j].φ[m]? = some (d - nuser) ∧ tr.aux[d - nuser]? = some a

theorem mentions_mono {ns ms : List Name} (h : ∀ c ∈ ns, c ∈ ms) :
    ∀ {e : VExpr}, mentions ms e = false → mentions ns e = false
  | .const c _, he => by
    simp only [mentions, List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at he ⊢
    exact fun x hx hxc => he x (h x hx) hxc
  | .app f a, he | .lam f a, he | .forallE f a, he => by
    simp only [mentions, Bool.or_eq_false_iff] at he ⊢
    exact ⟨mentions_mono h he.1, mentions_mono h he.2⟩
  | .bvar _, _ | .sort _, _ => rfl

structure Slot (rec : List RBlock) (n : Nat) (tr : Translated) (b : SBlock) (nuser : Nat)
    (fams : List Fam) (a : Aux) (J : Name) (lv : List VLevel) (Ds : List VExpr) (r : RBlock)
    (m d : Nat) : Prop where
  link : FamLink rec tr nuser fams a lv Ds r m d
  mem : r ∈ rec
  m_lt : m < r.b.ntypes
  nameJ : (r.b.types[m]!).name = J
  key : ∃ k, r.slotKey m = some k ∧ a.key.EqL (atKey lv Ds 0 k)
  hidden : ∀ D ∈ Ds, mentions (keyHidden tr b nuser) D = false
  hd : d < b.ntypes
  name : (b.types[d]!).name = a.name
  nDs : Ds.length = r.b.nparams
  indices : EqLTel lv Ds 0 (b.types[d]!).indices (r.b.types[m]!).indices
  nctors : (b.types[d]!).ctors.length = (r.b.types[m]!).ctors.length
  ctor_name : ∀ q < (b.types[d]!).ctors.length,
    ((b.types[d]!).ctors[q]!).name = (((r.info m).ctors[q]!).1).replacePrefix J a.name
  ctor_restore : ∀ q < (b.types[d]!).ctors.length,
    (((b.types[d]!).ctors[q]!).name).replacePrefix a.name J = ((r.info m).ctors[q]!).1
theorem Slot.dsfree {rec : List RBlock} {n : Nat} {tr : Translated} {b : SBlock} {nuser : Nat}
    {fams : List Fam} {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr} {r : RBlock}
    {m d : Nat} (hs : Slot rec n tr b nuser fams a J lv Ds r m d) :
    ∀ D ∈ Ds, mentions (tr.aux.map (·.name)) D = false :=
  fun D hD => mentions_mono (fun c hc => by simp [keyHidden, auxNames, hc]) (hs.hidden D hD)

theorem Slot.read {V : Type _} [SetTheory V] {M : CInterp V} {env : VEnv} {MJ : CInterp V}
    {envJ envJ₁ : VEnv} {rec : List RBlock} {n : Nat} {tr : Translated} {b : SBlock} {nuser : Nat}
    {fams : List Fam} {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr} {r : RBlock}
    {m d : Nat} (hs : Slot rec n tr b nuser fams a J lv Ds r m d)
    (cJ : CanonR M env r MJ envJ envJ₁) :
    ∃ k, r.slotKey m = some k ∧ a.key.EqL (atKey lv Ds 0 k) ∧ k.ClosedN r.b.nparams ∧
      ConstsIn (Dom env) k ∧ (∃ c us as, k = appN (.const c us) as) ∧
      ∀ ls ρ, ls.length = r.b.uvars → Ext MJ ls r.b.params [] ρ →
        interp M ls k ρ.reverse = ρ.foldl app (M₁ MJ r.b (carrierFn MJ r.b)
            (r.b.types[m]!).name ls) := by
  obtain ⟨k, hk, he⟩ := hs.key
  obtain ⟨k', hk', h1, h2, h3, h4⟩ := cJ.slots m hs.m_lt
  rw [hk] at hk'; cases hk'
  exact ⟨k, hk, he, h1, h2, h3, h4⟩

/-! ## The index sets of an auxiliary -/

section Index
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
  {MJ : CInterp V} {envJ envJ₁ : VEnv} {rec : List RBlock} {n : Nat} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr}
      {r : RBlock} {m d : Nat}

theorem getElem!_mem' {α : Type _} [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    l[i]! ∈ l := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

include S in
theorem agree_J (cJ : CanonR M env r MJ envJ envJ₁) {C : List Nat → List V → Nat → V} {c : Name}
    (hc : Dom envJ c) : M₁ M b C c = MJ c :=
  (S.agree (Dom.mono cJ.le hc)).trans (cJ.agree c hc)

include S in
theorem aux_Is (cJ : CanonR M env r MJ envJ envJ₁) (hs : Slot rec n tr b nuser fams a J lv Ds r m d)
    (hm : m < r.b.ntypes) (C : List Nat → List V → Nat → V) (ls : List Nat) (ρp : List V) :
    Is M ls b ρp d = Is MJ (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b C) ls Ds ρp) m := by
  unfold Is
  obtain ⟨hlen, hget⟩ := EqLTel.get hs.indices
  apply SetTheory.ext; intro t
  rw [mem_extSet, mem_extSet]
  refine exists_congr fun zs => and_congr_left fun _ => ext_transfer hlen fun i hi hi' ys hys => ?_
  have hiJ : i < (r.b.types[m]!).indices.length := hi'
  have hys' : ys.reverse.length = i := by
    rw [List.length_reverse, Ext.length_eq _ _ hys, List.length_take]; omega
  have hX : ∀ A ∈ (b.types[d]!).indices, ConstsIn (Dom env) A := S.indices_consts hs.hd
  have e1 : interp M ls (b.types[d]!).indices[i] (ys.reverse ++ ρp) =
      interp (M₁ M b C) ls (b.types[d]!).indices[i] (ys.reverse ++ ρp) :=
    (interp_congr ((S.free₀ (C := C) (hX _ (List.getElem_mem hi))).mono fun _ h => h.symm) _)
  have hc := cJ.setting.indices_closed hm hiJ
  rw [← hs.nDs, Nat.add_comm, ← getElem_eq_getElem! hiJ] at hc
  rw [e1, interp_EqL _ _ (hget i hi hi') _, Nat.zero_add,
    interp_atKey (M₁ M b C) ls lv Ds ρp hc ys.reverse hys']
  have hJc : ConstsIn (Dom envJ) ((r.b.types[m]!).indices[i]) :=
    cJ.setting.indices_consts hm _ (List.getElem_mem hiJ)
  exact interp_congr (hJc.mono fun _ h => agree_J S cJ h) _

end Index

end Soulgem.Nested
