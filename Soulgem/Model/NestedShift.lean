import Soulgem.Model.NestedRec

/-! # Restoration at shifted levels -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

def shiftTr (tr : Translated) (us : List VLevel) : Translated :=
  { tr with aux := tr.aux.map fun (a : Aux) => { a with key := a.key.instL us } }

theorem appN_instL (us : List VLevel) : ∀ (as : List VExpr) (f : VExpr),
    (appN f as).instL us = appN (f.instL us) (as.map (·.instL us))
  | [], _ => rfl
  | a :: as, f => by
    simp only [appN, List.foldl_cons, List.map_cons] at *
    exact appN_instL us as (.app f a)

theorem headArgs_instL (us : List VLevel) : ∀ e : VExpr,
    headArgs (e.instL us) = ((headArgs e).1.instL us, (headArgs e).2.map (·.instL us))
  | .app f a => by
    simp only [VExpr.instL, headArgs, headArgs_instL us f, List.map_append, List.map_cons,
      List.map_nil]
  | .bvar _ | .sort _ | .const _ _ | .lam _ _ | .forallE _ _ => by
    simp only [VExpr.instL, headArgs, List.map_nil]

theorem shiftTr_find (tr : Translated) (us : List VLevel) (c : Name) :
    ((shiftTr tr us).aux.find? (·.name == c)).isSome = (tr.aux.find? (·.name == c)).isSome := by
  simp only [shiftTr, List.find?_map, Option.isSome_map]
  rfl

theorem shiftTr_auxOfCtor (tr : Translated) (us : List VLevel) (c : Name) :
    (shiftTr tr us).auxOfCtor? c =
      (tr.auxOfCtor? c).map fun (a : Aux) => { a with key := a.key.instL us } := by
  simp only [Translated.auxOfCtor?, shiftTr, List.find?_map]
  rfl

variable {M : CInterp V} {ls₀ ls : List Nat} {tr : Translated} {auxRec : List (Name × Name)}
  {ns ms : List Name} {k n : Nat} {Q : List V → Prop}

theorem _root_.Soulgem.RestoreHyp.shift (H : RestoreHyp M M ls₀ tr [] ns ms
    (ownLevels k) n Q)
    (bl : List VLevel) (hls : ls₀ = bl.map (VLevel.eval ls)) (hk : ls₀.length = k)
    (hms : ∀ p ∈ auxRec, p.1 ∈ ms) (hns : ∀ p ∈ auxRec, p.1 ∉ ns)
    (hother : ∀ c, c ∉ ns → M c = M (rename auxRec c)) :
    RestoreHyp M M ls (shiftTr tr bl) auxRec ns ms bl n Q where
  ns_iff := fun c => by
    rw [shiftTr_find, shiftTr_auxOfCtor, Option.isSome_map]
    exact H.ns_iff c
  ms_ns := H.ms_ns
  ms_rec := hms
  rec_ns := hns
  key_head := fun a' ha' => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨Ic, Ils, Ds, hh⟩ := H.key_head a ha
    exact ⟨Ic, Ils.map (·.inst bl), Ds.map (·.instL bl), by
      simp only [headArgs_instL, hh, VExpr.instL]⟩
  other := hother
  closed := fun a' ha' => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    exact (H.closed a ha).instL
  aux := fun a' ha' xs hxs hQ => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    have h := H.aux a ha xs hxs hQ
    rw [show (ownLevels k).map (fun x => VLevel.eval ls₀ x) = ls₀ from map_eval_params hk] at h
    dsimp only
    rw [interp_instL, ← hls]
    exact h
  ctor := fun c a' hca Ic Ils' Ds' hk' xs hxs hQ => by
    rw [shiftTr_auxOfCtor] at hca
    cases hca0 : tr.auxOfCtor? c with
    | none => rw [hca0] at hca; cases hca
    | some a =>
      rw [hca0] at hca
      simp only [Option.map_some, Option.some.injEq] at hca
      subst hca
      obtain ⟨Ic₀, Ils, Ds, hh⟩ := H.key_head a (List.mem_of_find?_eq_some hca0)
      have hk'' := hk'
      simp only [headArgs_instL, hh, VExpr.instL, Prod.mk.injEq, VExpr.const.injEq] at hk''
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk''
      have h := H.ctor c a hca0 Ic₀ Ils Ds hh xs hxs hQ
      rw [show (ownLevels k).map (fun x => VLevel.eval ls₀ x) = ls₀ from map_eval_params hk] at h
      dsimp only
      rw [← hls, h, show VExpr.const (c.replacePrefix a.name Ic₀) (Ils.map (·.inst bl)) =
        (VExpr.const (c.replacePrefix a.name Ic₀) Ils).instL bl from rfl, ← appN_instL,
        interp_instL, ← hls]

theorem mem_auxRecTable {b : SBlock} {nuser : Nat} {p : Name × Name}
    (hp : p ∈ auxRecTable b nuser) : ∃ i, i < b.ntypes - nuser ∧ p.1 = b.recName (nuser + i) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem auxRec_mem_recs {b : SBlock} {nuser : Nat} {p : Name × Name}
    (hp : p ∈ auxRecTable b nuser) : p.1 ∈ (List.range b.ntypes).map b.recName := by
  obtain ⟨i, hi, he⟩ := mem_auxRecTable hp
  rw [he]; exact recName_mem (by omega)

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
  (hRN : RecNames b nuser = true)
  (hfin : ∀ x ∈ (auxRecTable b nuser).map (·.2), env.constants x = none)
  (hrecu : ∀ d < nuser, env.constants (b.recName d) = none)
  (hctu : ∀ c ∈ (b.types.take nuser).flatMap (·.ctors), env.constants c.name = none)
include N

theorem auxRec_not_ns (hRN : RecNames b nuser = true) {p : Name × Name}
    (hp : p ∈ auxRecTable b nuser) : p.1 ∉ auxNs tr b nuser := by
  have RN := RecNames.spec hRN
  have hr := auxRec_mem_recs hp
  unfold auxNs
  intro h
  rcases List.mem_append.mp h with h | h
  · refine RN.rec_names _ hr ?_
    rw [N.names_split]; exact List.mem_append_right _ h
  · refine RN.rec_ctors _ hr ?_
    obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp h
    obtain ⟨c, hc, he⟩ := List.mem_map.mp hc
    rw [← he]
    exact List.mem_map_of_mem (List.mem_flatMap.mpr ⟨t, List.mem_of_mem_drop ht, hc⟩)

omit N in
theorem Mrec_rename (hRN : RecNames b nuser = true) (c : Name) :
    Mrec M b nuser c = Mrec M b nuser (rename (auxRecTable b nuser) c) := by
  have RN := RecNames.spec hRN
  unfold rename
  cases h : (auxRecTable b nuser).find? (·.1 == c) with
  | none => rfl
  | some p =>
    have hp := List.mem_of_find?_eq_some h
    have hpc : p.1 = c := by simpa using List.find?_some h
    show _ = Mrec M b nuser p.2
    rw [Mrec_fin RN.fin_nodup hp, ← hpc,
      Mrec_of_not_fin fun hf => RN.fin_recs _ hf (auxRec_mem_recs hp)]

include hRN hfin hrecu hctu in
theorem restoreHyp_rec (ls' : List Nat) :
    RestoreHyp (Mrec M b nuser) (Mrec M b nuser) ls' (shiftTr tr b.blockLevels)
        (auxRecTable b nuser)
      (auxNs tr b nuser) (auxMs tr b nuser) b.blockLevels b.nparams
      (fun xs => Ext M (blev b ls') b.params [] xs) :=
  (N.restoreHyp_ctor hRN hfin hrecu hctu (blev_length b ls')).shift b.blockLevels rfl
    (blev_length b ls')
    (fun p hp => by
      obtain ⟨i, hi, he⟩ := mem_auxRecTable hp
      unfold auxMs; rw [he]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    (fun _ hp => N.auxRec_not_ns hRN hp)
    (fun c _ => Mrec_rename hRN c)

end NWF

end Soulgem.Nested
