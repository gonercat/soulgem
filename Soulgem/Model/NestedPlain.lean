import Soulgem.Model.NestedCorr
import Soulgem.Model.NestedLe

/-! # Nested blocks: plain container fields, read through restoration -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

theorem findName_getElem_of_lt : ∀ {ns : List Name} {c : Name} (h : findName ns c < ns.length),
    ns[findName ns c] = c
  | [], _, h => absurd h (by simp [findName])
  | n :: ns, c, h => by
    unfold findName at h ⊢
    by_cases e : n = c
    · simp [e]
    · simp only [e, ite_false] at h ⊢
      simpa using findName_getElem_of_lt (ns := ns) (c := c) (by simpa using h)

theorem M₁_agree {M : CInterp V} {b : SBlock} {C₁ C₂ : List Nat → List V → Nat → V} {c : Name}
    (h : ∀ s < b.ntypes, (b.types[s]!).name = c → ∀ ls ρ, C₁ ls ρ s = C₂ ls ρ s) :
    M₁ M b C₁ c = M₁ M b C₂ c := by
  funext ls'
  unfold M₁
  by_cases hlt : findName b.names c < b.ntypes
  · simp only [ite_eq_left hlt]
    have hlt' : findName b.names c < b.names.length := by rw [names_length]; exact hlt
    have hname : (b.types[findName b.names c]!).name = c := by
      have := findName_getElem_of_lt hlt'
      simp only [SBlock.names, List.getElem_map] at this
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact this
    unfold former
    congr 1; funext ρp; congr 1; funext ρ
    rw [h _ hlt hname]
  · simp only [ite_eq_right hlt]

section Restore
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
  {tr : Translated} {nuser : Nat}

abbrev auxNs (tr : Translated) (b : SBlock) (nuser : Nat) : List Name := auxNames tr b nuser

def auxMs (tr : Translated) (b : SBlock) (nuser : Nat) : List Name :=
  auxNs tr b nuser ++ (List.range (b.ntypes - nuser)).map fun i => b.recName (nuser + i)

include S in
theorem field_restoreSafe (hRS : RestoreSafe tr b nuser = true) {d : Nat} (_hd : nuser ≤ d)
    (hdl : d < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[d]!).ctors) {k : Nat}
    (hk : k < c.fields.length) :
    restoreSafe (auxNs tr b nuser) (auxMs tr b nuser) (ownLevels b.uvars) b.nparams
      (c.fields[k]!).ty (b.nparams + k) = true := by
  unfold RestoreSafe at hRS
  simp only [Bool.and_eq_true, List.all_eq_true] at hRS
  have h := hRS.1 _ (getElem!_mem' hdl) c hc
  obtain ⟨Ps, hPl, hty, _⟩ := S.ctor_shape d hdl c hc
  unfold restoreSafeTop at h
  rw [hty, ← hPl] at h
  have h2 := restoreSafeTop_forallTel _ _ _ _ Ps _ 0 h
  rw [Nat.zero_add, hPl] at h2
  have h3 := (restoreSafe_forallTel _ _ _ _ (c.fields.map (·.ty)) _ _ h2).1 k (by simpa using hk)
  rw [getElem!_map' _ hk] at h3
  exact h3

end Restore

section Canon
variable {M : CInterp V} {b : SBlock} {tr : Translated} {ns ms : List Name}
  {C : List Nat → List V → Nat → V} {ls : List Nat} {ps : List V}

open Classical in
noncomputable def ctorTarget (M₀ : CInterp V) (ls : List Nat) (tr : Translated) (ps : List V)
    (c : Name) : V :=
  match tr.auxOfCtor? c with
  | some a => match headArgs a.key with
    | (.const Ic Ils, Ds') => interp M₀ ls (appN (.const (c.replacePrefix a.name Ic) Ils)
        Ds') ps.reverse
    | _ => pt
  | none => pt

open Classical in
noncomputable def canonOverride (M : CInterp V) (b : SBlock) (C : List Nat → List V → Nat → V)
    (ls : List Nat) (tr : Translated) (ps : List V) : CInterp V := fun c lvls =>
  if (tr.auxOfCtor? c).isSome then
    Soulgem.lamTel M ls b.params (fun _ => ctorTarget (M₁ M b C) ls tr ps c) []
  else M₁ M b C c lvls

theorem canonOverride_of_none {c : Name} (h : tr.auxOfCtor? c = none) :
    canonOverride M b C ls tr ps c = M₁ M b C c := by
  funext lvls; simp [canonOverride, h]

theorem restoreHyp_canon (hl : ls.length = b.uvars) (hps : Ext M ls b.params [] ps)
    (hns : ∀ c, c ∈ ns ↔ ((tr.aux.find? (·.name == c)).isSome ∨ (tr.auxOfCtor? c).isSome))
    (hms : ∀ c ∈ ns, c ∈ ms)
    (hdisj : ∀ c a, tr.auxOfCtor? c = some a → (tr.aux.find? (·.name == c)) = none)
    (hk : ∀ a ∈ tr.aux, ∃ Ic Ils Ds, headArgs a.key = (.const Ic Ils, Ds))
    (hcl : ∀ a ∈ tr.aux, a.key.ClosedN b.nparams)
    (hkeys : ∀ a ∈ tr.aux,
      ps.foldl app (M₁ M b C a.name ls) = interp (M₁ M b C) ls a.key ps.reverse) :
    RestoreHyp (canonOverride M b C ls tr ps) (M₁ M b C) ls tr [] ns ms (ownLevels b.uvars)
      b.nparams (· = ps) where
  ns_iff := hns
  ms_ns := hms
  ms_rec := fun _ h => absurd h (by simp)
  rec_ns := fun _ h => absurd h (by simp)
  key_head := hk
  other := fun c hc => by
    have hnone : tr.auxOfCtor? c = none := by
      cases h : tr.auxOfCtor? c with
      | none => rfl
      | some _ => exact absurd ((hns c).mpr (Or.inr (by simp [h]))) hc
    rw [canonOverride_of_none hnone, rename_of_not_key fun _ h => absurd h (by simp)]
  closed := hcl
  aux := fun a ha xs _ hxs => by
    subst hxs
    have hnone : tr.auxOfCtor? a.name = none := by
      cases h : tr.auxOfCtor? a.name with
      | none => rfl
      | some a' =>
        have := hdisj _ _ h
        rw [List.find?_eq_none] at this
        exact absurd (by simp : (a.name == a.name) = true) (this a ha)
    rw [canonOverride_of_none hnone, ownLevels_eval hl]
    exact hkeys a ha
  ctor := fun c a hc Ic Ils Ds hkey xs _ hxs => by
    subst hxs
    have hsome : (tr.auxOfCtor? c).isSome := by simp [hc]
    simp only [canonOverride, hsome, ite_true]
    rw [apps_lamTel hps]
    simp only [ctorTarget, hc, hkey]

end Canon

section Restored
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} {MJ : CInterp V} {envJ envJ₁ : VEnv}
  {rec : List RBlock} {n : Nat} {tr : Translated} {a : Aux} {J : Name} {lv : List VLevel}
  {Ds : List VExpr} {r : RBlock} {m d : Nat} {ns ms : List Name} {us : List VLevel}

theorem field_restored (SJ : Setting MJ envJ envJ₁ r.b)
    (hs : Slot rec n tr b nuser fams a J lv Ds r m d) (hm : m < r.b.ntypes) {q : Nat}
    (hq : q < (b.types[d]!).ctors.length) {k : Nat}
    (hkJ : k < ((r.b.types[m]!).ctors[q]!).fields.length)
    (hfc : (tr.restoreBody [] n (((b.types[d]!).ctors[q]!).fields[k]!).ty (n + k)).EqL
      (atKey lv Ds k (((r.b.types[m]!).ctors[q]!).fields[k]!).ty))
    {M₂ M' MJ' : CInterp V} {ls : List Nat} {ps : List V}
    (H : RestoreHyp M₂ M' ls tr [] ns ms us n (· = ps))
    (hsafe : restoreSafe ns ms us n (((b.types[d]!).ctors[q]!).fields[k]!).ty (n + k) = true)
    (hM₂ : ConstsIn (fun c => M₂ c = M' c) (((b.types[d]!).ctors[q]!).fields[k]!).ty)
    (hagr : ConstsIn (fun c => M' c = MJ' c) (((r.b.types[m]!).ctors[q]!).fields[k]!).ty)
    (hpl : ps.length = n) (ys : List V) (hys : ys.length = k) :
    interp M' ls (((b.types[d]!).ctors[q]!).fields[k]!).ty (ys.reverse ++ ps.reverse) =
      interp MJ' (lv.map (VLevel.eval ls)) (((r.b.types[m]!).ctors[q]!).fields[k]!).ty
        (ys.reverse ++ keyArgs M' ls Ds ps.reverse) := by
  have hqJ : q < (r.b.types[m]!).ctors.length := hs.nctors ▸ hq
  have hcl : (((r.b.types[m]!).ctors[q]!).fields[k]!).ty.ClosedN (k + Ds.length) := by
    rw [hs.nDs, Nat.add_comm]
    exact (SJ.field_scoped (P := Dom envJ₁) (fun _ h => h) hm (getElem!_mem' hqJ) hkJ).1
  rw [← interp_congr hM₂]
  rw [← H.interp_restoreBody _ (d := n + k) (Nat.le_add_right n k) (by simp [hys, hpl]; omega)
    (by simp [hpl]) hsafe]
  rw [interp_EqL _ _ hfc]
  exact interp_key M' MJ' ls lv Ds hcl hagr ys.reverse (by simp [hys]) ps.reverse

end Restored

section PlainField
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} {MJ : CInterp V} {envJ envJ₁ : VEnv}
  {rec : List RBlock} {n : Nat} {tr : Translated} {a : Aux} {J : Name} {lv : List VLevel}
  {Ds : List VExpr} {r : RBlock} {m d : Nat} {ns ms : List Name} {us : List VLevel}

theorem fdom_plain_corr (S : Setting M env env₁ b) (SJ : Setting MJ envJ envJ₁ r.b)
    (hs : Slot rec n tr b nuser fams a J lv Ds r m d)
    (hn : n = b.nparams) (hm : m < r.b.ntypes) {q : Nat} (hq : q < (b.types[d]!).ctors.length)
    {k : Nat} (hk : k < ((b.types[d]!).ctors[q]!).fields.length)
    (hkJ : k < ((r.b.types[m]!).ctors[q]!).fields.length)
    (hfc : (tr.restoreBody [] n (((b.types[d]!).ctors[q]!).fields[k]!).ty (n + k)).EqL
      (atKey lv Ds k (((r.b.types[m]!).ctors[q]!).fields[k]!).ty))
    {X XB Y : Nat → V} {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars)
    (hps : Ext M ls b.params [] ps)
    (hX : InTupleSpace (lev ls b) b.ntypes (Is M ls b ps.reverse) X)
    (hXB : InTupleSpace (lev ls b) b.ntypes (Is M ls b ps.reverse) XB)
    {w : VExpr} (hw : (((r.b.types[m]!).ctors[q]!).fields[k]!).cert = .plain w)
    (hagX : ConstsIn (fun c => ∀ s < b.ntypes, (b.types[s]!).name = c → X s = XB s)
      (((b.types[d]!).ctors[q]!).fields[k]!).ty)
    {M₂ : CInterp V} (H : RestoreHyp M₂ (M₁ M b (patch M b ls ps.reverse XB)) ls tr [] ns ms
        us n (· = ps))
    (hsafe : restoreSafe ns ms us n (((b.types[d]!).ctors[q]!).fields[k]!).ty (n + k) = true)
    (hM₂ : ConstsIn (fun c => M₂ c = M₁ M b (patch M b ls ps.reverse XB) c)
      (((b.types[d]!).ctors[q]!).fields[k]!).ty)
    (hagr : ConstsIn (fun c => M₁ M b (patch M b ls ps.reverse XB) c =
        M₁ MJ r.b (carrierFn MJ r.b) c)
      (((r.b.types[m]!).ctors[q]!).fields[k]!).ty)
    (hlJ : (lv.map (VLevel.eval ls)).length = r.b.uvars)
    (hpsJ : Ext MJ (lv.map (VLevel.eval ls)) r.b.params []
      (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse).reverse)
    (ys : List V) (hys : ys.length = k)
    (hfit : FFit M ls X ((((b.types[d]!).ctors[q]!).fields).take k) ps.reverse ys)
    (hfitJ : FFit MJ (lv.map (VLevel.eval ls))
      (carrier MJ (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds
          ps.reverse))
      ((((r.b.types[m]!).ctors[q]!).fields).take k)
      (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse) ys) :
    fdom M ls X (((b.types[d]!).ctors[q]!).fields[k]!) (ys.reverse ++ ps.reverse) =
      fdom MJ (lv.map (VLevel.eval ls)) Y (((r.b.types[m]!).ctors[q]!).fields[k]!)
        (ys.reverse ++ keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse) := by
  have hqJ : q < (r.b.types[m]!).ctors.length := hs.nctors ▸ hq
  have hpl : ps.length = b.nparams := by rw [Ext.length_eq _ _ hps]; rfl
  generalize hρJ : keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse = ρJ at *
  have hCX := patch_tupleFn (M := M) (b := b) (ls₀ := ls) (ρ₀ := ps.reverse) hX
  have hsat : Sat (M₁ M b (patch M b ls ps.reverse X)) ls
      (Setting.fctx b ((b.types[d]!).ctors[q]!) k) (ps ++ ys).reverse := by
    have := (S.ffit_iff_sat hCX hl hs.hd (getElem!_mem' hq) hps k (Nat.le_of_lt hk) ys hys).mp
      (by rw [patch_at]; exact hfit)
    simpa using this
  have e1 := S.interp_field hCX hl hs.hd (getElem!_mem' hq) hk (zs := ps ++ ys)
    (by simp [hpl, hys]) hsat (by simpa [hpl] using hps)
  simp only [List.reverse_append, List.take_left' hpl, patch_at] at e1
  rw [← e1]
  rw [interp_congr (hagX.mono fun c h => M₁_agree (C₁ := patch M b ls ps.reverse X)
      (C₂ := patch M b ls ps.reverse XB) fun s hsl hname ls' ρ' => by
    by_cases h' : ls' = ls ∧ ρ' = ps.reverse
    · obtain ⟨rfl, rfl⟩ := h'; rw [patch_at, patch_at]; exact h s hsl hname
    · simp [patch, h'])]
  have e3 := field_restored SJ hs hm hq hkJ hfc H hsafe hM₂ hagr (hn ▸ hpl) ys hys
  rw [hρJ] at e3
  rw [e3]
  subst hρJ
  have hsatJ : Sat (M₁ MJ r.b (carrierFn MJ r.b)) (lv.map (VLevel.eval ls))
      (Setting.fctx r.b ((r.b.types[m]!).ctors[q]!) k)
      ((keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse).reverse ++ ys).reverse := by
    have := (SJ.ffit_iff_sat (carrier_tupleFn (M := MJ) (b := r.b)) hlJ hm (getElem!_mem' hqJ) hpsJ
      k (Nat.le_of_lt hkJ) ys hys).mp (by simpa using hfitJ)
    simpa using this
  have hpsJl : (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse).reverse.length =
      r.b.nparams := by rw [List.length_reverse, keyArgs_length, hs.nDs]
  have e2 := SJ.interp_field (carrier_tupleFn (M := MJ) (b := r.b)) hlJ hm (getElem!_mem' hqJ) hkJ
    (zs := (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse).reverse ++ ys)
    (by simp [hpsJl, hys]) hsatJ (by simpa [List.take_left' hpsJl] using hpsJ)
  simp only [List.reverse_append, List.reverse_reverse] at e2
  rw [e2]
  simp only [fdom, hw]

end PlainField

end Soulgem.Nested
