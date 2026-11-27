import Soulgem.Model.NestedEq

/-! # Auxiliary constructors read as their container constructors -/

namespace Soulgem.BlockModel.Setting
open ConLeche ConLeche.SetTheory Lean4Lean Spec
universe u
variable {V : Type u} [SetTheory V]
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem params_sat {C : List Nat → List V → Nat → V} {ls : List Nat} {ps : List V}
    (hps : Ext M ls b.params [] ps) : Sat (M₁ M b C) ls b.params.reverse ps.reverse := by
  have := Sat.of_ext (Γ := []) (ρ := []) trivial
    ((Ext.congrM (fun _ h => h) fun A hA => (S.free₀ (C := C) (S.params_consts' A hA)).mono
      fun _ h => h.symm).mp hps)
  simpa using this

theorem params_ext {C : List Nat → List V → Nat → V} {ls : List Nat} {ps : List V}
    (hps : Ext M ls b.params [] ps) : Ext (M₁ M b C) ls b.params [] ps :=
  (Ext.congrM (fun _ h => h) fun A hA => (S.free₀ (C := C) (S.params_consts' A hA)).mono
    fun _ h => h.symm).mp hps

omit S in
theorem ctorVal_apps {M' : CInterp V} {ls : List Nat} {ps : List V} {q : Nat} {c : SCtor}
    (hps : Ext M' ls b.params [] ps) :
    ps.foldl app (ctorVal b M' ls q c) =
      Soulgem.lamTel M' ls (c.fields.map (·.ty))
        (fun ρ' => BlockSem.enc ls b q ((ρ'.take c.fields.length).reverse)) ps.reverse := by
  unfold ctorVal; rw [apps_lamTel hps, List.append_nil]

end Soulgem.BlockModel.Setting

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

theorem getElem!_take_of_lt {α : Type _} [Inhabited α] {l : List α} {i k : Nat} (h : k < i) :
    (l.take i)[k]! = l[k]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take, ite_eq_left h]

theorem take_take_of_le {α : Type _} {l : List α} {i k : Nat} (h : k ≤ i) :
    (l.take i).take k = l.take k := by
  rw [List.take_take]; congr 1; omega

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
include N

theorem fdom_eq {a : Aux} (ha : a ∈ tr.aux) {J : Name} {lv : List VLevel} {Ds : List VExpr}
    {r : RBlock} {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d)
    {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars) (hps : Ext M ls b.params [] ps)
    {q : Nat} (hq : q < (b.types[d]!).ctors.length) {k : Nat}
    (hk : k < ((b.types[d]!).ctors[q]!).fields.length) (ys : List V) (hys : ys.length = k)
    (hfit : FFit M ls (carrier M ls b ps.reverse) (((b.types[d]!).ctors[q]!).fields.take k)
      ps.reverse ys)
    (hfitJ : FFit (MJf r) (lv.map (VLevel.eval ls))
      (carrier (MJf r) (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b (carrierFn M b)) ls Ds
          ps.reverse))
      (((r.b.types[m]!).ctors[q]!).fields.take k) (keyArgs (M₁ M b (carrierFn M b)) ls Ds
          ps.reverse) ys) :
    fdom M ls (carrier M ls b ps.reverse) (((b.types[d]!).ctors[q]!).fields[k]!)
        (ys.reverse ++ ps.reverse) =
      fdom (MJf r) (lv.map (VLevel.eval ls))
        (carrier (MJf r) (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b (carrierFn M b)) ls Ds
            ps.reverse))
        (((r.b.types[m]!).ctors[q]!).fields[k]!)
        (ys.reverse ++ keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse) := by
  obtain ⟨j, hj, hlv, hDs, hr', -, hφ, -⟩ := hs.link
  have F := N.frame ha hs hj hlv hDs hr' hφ hl hps
  have hkp := N.keyArgs_patch hs.dsfree ls ps ps.reverse
  rw [← hkp] at hfitJ ⊢
  have hcar := carrier_mem (M := MJf r) (ls := lv.map (VLevel.eval ls)) (b := r.b)
    (ρp := keyArgs (M₁ M b (patch M b ls ps.reverse (allKeys M b rec nuser fams MJf ls ps))) ls
        Ds ps.reverse)
  exact F.fdom_corr (X := carrier M ls b ps.reverse) carrier_mem hcar (TupleLe.refl _ _ _)
    (fun m' g hm' hg => by
      have hd : nuser + g < b.ntypes := by
        obtain ⟨_, _, hsp⟩ := N.slotSpec hj hr' hm'
        rw [getElem!_of_some hg] at hsp; exact hsp.hd
      rw [N.carrier_allKeys hl hps hd, N.allKeys_slot hj hr' hg, hlv, hDs, hkp])
    (fun q _ k _ w _ => (N.S.field_scoped (P := fun _ => True) (fun _ _ => trivial) hs.hd
      (getElem!_mem' (by assumption)) (by assumption)).2.mono fun _ _ s hs' _ =>
        N.carrier_allKeys hl hps hs')
    hq hk ys hys hfit hfitJ

theorem ffit_prefix {a : Aux} (ha : a ∈ tr.aux) {J : Name} {lv : List VLevel} {Ds : List VExpr}
    {r : RBlock} {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d)
    {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars) (hps : Ext M ls b.params [] ps)
    {q : Nat} (hq : q < (b.types[d]!).ctors.length) {i : Nat}
    (hi : i ≤ ((b.types[d]!).ctors[q]!).fields.length) (ys : List V) :
    FFit M ls (carrier M ls b ps.reverse) (((b.types[d]!).ctors[q]!).fields.take i) ps.reverse ys ↔
      FFit (MJf r) (lv.map (VLevel.eval ls))
        (carrier (MJf r) (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b (carrierFn M b)) ls Ds
            ps.reverse))
        (((r.b.types[m]!).ctors[q]!).fields.take i) (keyArgs (M₁ M b (carrierFn M b)) ls Ds
            ps.reverse) ys := by
  obtain ⟨_, _, _, F⟩ := N.frameOf ha hs hl hps
  have spec := ctorCorr_spec (F.hcc q hq)
  refine ffit_congr _ _ _ _ (by simp only [List.length_take, spec.1])
    (fun k hk ys' hys' hfit hfitJ => ?_) ys
  have hki : k < i := by simp only [List.length_take] at hk; omega
  rw [take_take_of_le (Nat.le_of_lt hki)] at hfit hfitJ
  rw [getElem!_take_of_lt hki, getElem!_take_of_lt hki]
  exact N.fdom_eq ha hs hl hps hq (by omega) ys' hys' hfit hfitJ

theorem ctor_body_eq {a : Aux} (ha : a ∈ tr.aux) {J : Name} {lv : List VLevel} {Ds : List VExpr}
    {r : RBlock} {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d)
    {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars) (hps : Ext M ls b.params [] ps)
    {q : Nat} (hq : q < (b.types[d]!).ctors.length) :
    Soulgem.lamTel (Setting.Mc M b) ls (((b.types[d]!).ctors[q]!).fields.map (·.ty))
        (fun ρ' => enc ls b q ((ρ'.take ((b.types[d]!).ctors[q]!).fields.length).reverse))
        ps.reverse =
      Soulgem.lamTel (Setting.Mc (MJf r) r.b) (lv.map (VLevel.eval ls))
        (((r.b.types[m]!).ctors[q]!).fields.map (·.ty))
        (fun ρ' => enc (lv.map (VLevel.eval ls)) r.b q
          ((ρ'.take ((r.b.types[m]!).ctors[q]!).fields.length).reverse))
        (keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse) := by
  obtain ⟨_, _, _, F⟩ := N.frameOf ha hs hl hps
  have S := N.S
  have hr := hs.mem
  have SJ := (N.canon r hr).setting
  have hm := NWF.m_lt hs
  have spec := ctorCorr_spec (F.hcc q hq)
  have hqJ : q < (r.b.types[m]!).ctors.length := hs.nctors ▸ hq
  have hmem : (b.types[d]!).ctors[q]! ∈ (b.types[d]!).ctors := getElem!_mem' hq
  have hmemJ : (r.b.types[m]!).ctors[q]! ∈ (r.b.types[m]!).ctors := getElem!_mem' hqJ
  have hkp := N.keyArgs_patch hs.dsfree ls ps ps.reverse
  have hpsJ : Ext (MJf r) (lv.map (VLevel.eval ls)) r.b.params []
      (keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse).reverse := by
    rw [← hkp]; exact F.hpsJ
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M ls hps]; rfl
  have hKlen : (keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse).length = r.b.nparams := by
    have := Ext.length_eq (MJf r) (lv.map (VLevel.eval ls)) hpsJ
    rw [List.length_reverse] at this; rw [this]; rfl
  refine lamTel_transfer (by simp only [List.length_map, spec.1]) (fun i hi hi' ys hys => ?_)
    (fun ys hys => ?_)
  · simp only [List.length_map] at hi hi'
    have hylen : ys.length = i := by
      rw [Ext.length_eq _ _ hys, List.length_take, List.length_map]; omega
    have hsatJ : Sat (Setting.Mc (MJf r) r.b) (lv.map (VLevel.eval ls))
        (Setting.fctx r.b ((r.b.types[m]!).ctors[q]!) i)
        (ys.reverse ++ keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse) := by
      have hP : Sat (Setting.Mc (MJf r) r.b) (lv.map (VLevel.eval ls)) r.b.params.reverse
          (keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse) := by
        have := SJ.params_sat (C := fun ls ρp => carrier (MJf r) ls r.b ρp) hpsJ
        rwa [List.reverse_reverse] at this
      have h := Sat.of_ext hP hys
      simpa only [Setting.fctx, List.reverse_append, List.map_take] using h
    have hfJ := (SJ.ffit_iff_sat (carrier_tupleFn _ _) F.hlJ hm hmemJ hpsJ i (by omega)
        ys hylen).mpr
      (by rw [List.reverse_reverse]; exact hsatJ)
    rw [List.reverse_reverse] at hfJ
    have hfit := (N.ffit_prefix ha hs hl hps hq (by omega) ys).mpr hfJ
    have hsat := (S.ffit_iff_sat (carrier_tupleFn _ _) hl hs.hd hmem hps i (by omega) ys
        hylen).mp hfit
    have e1 := S.interp_field (carrier_tupleFn _ _) hl hs.hd hmem (a := i) (by omega)
      (zs := ps ++ ys) (by simp [hplen, hylen]) (by simpa using hsat)
      (by rw [List.take_left' hplen]; exact hps)
    have e2 := SJ.interp_field (carrier_tupleFn _ _) F.hlJ hm hmemJ (a := i) (by omega)
      (zs := (keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse).reverse ++ ys)
      (by simp [hKlen, hylen]) (by simpa using hsatJ)
      (by rw [List.take_left' (by rw [List.length_reverse, hKlen])]; exact hpsJ)
    simp only [List.reverse_append, List.reverse_reverse, List.take_left' hplen,
      List.take_left' (show (keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse).reverse.length =
        r.b.nparams by rw [List.length_reverse, hKlen])] at e1 e2
    rw [List.getElem_map, List.getElem_map, getElem_eq_getElem! (by omega),
      getElem_eq_getElem! (by omega), e1, e2]
    exact N.fdom_eq ha hs hl hps hq (by omega) ys hylen
      ((S.ffit_iff_sat (carrier_tupleFn _ _) hl hs.hd hmem hps i (by omega) ys hylen).mpr hsat) hfJ
  · have hylen : ys.length = ((r.b.types[m]!).ctors[q]!).fields.length := by
      rw [Ext.length_eq _ _ hys, List.length_map]
    rw [List.take_left' (by rw [List.length_reverse, hylen, spec.1]),
      List.take_left' (by rw [List.length_reverse, hylen])]
    unfold enc
    rw [N.lev_aux hs.link ls]

theorem aux_ctor_val {a : Aux} (ha : a ∈ tr.aux) {J : Name} {lv : List VLevel} {Ds : List VExpr}
    {r : RBlock} {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d)
    {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars) (hps : Ext M ls b.params [] ps)
    {q : Nat} (hq : q < (b.types[d]!).ctors.length) :
    ps.foldl app (Setting.ctorVal b (Setting.Mc M b) ls q ((b.types[d]!).ctors[q]!)) =
      (keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse).reverse.foldl app
        (Setting.ctorVal r.b (Setting.Mc (MJf r) r.b) (lv.map (VLevel.eval ls)) q
          ((r.b.types[m]!).ctors[q]!)) := by
  obtain ⟨_, _, _, F⟩ := N.frameOf ha hs hl hps
  have hr := hs.mem
  have SJ := (N.canon r hr).setting
  have hkp := N.keyArgs_patch hs.dsfree ls ps ps.reverse
  have hpsJ : Ext (MJf r) (lv.map (VLevel.eval ls)) r.b.params []
      (keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse).reverse := by
    rw [← hkp]; exact F.hpsJ
  rw [Setting.ctorVal_apps (N.S.params_ext hps), Setting.ctorVal_apps (SJ.params_ext hpsJ),
    List.reverse_reverse]
  exact N.ctor_body_eq ha hs hl hps hq

end NWF
end Soulgem.Nested
