import Soulgem.Model.BlockIota
import Soulgem.Model.NestedData
import Soulgem.Spec.Eta

/-! # The structure-eta law -/

namespace Soulgem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V]

namespace BlockModel
open BlockSem

theorem etaCtor_spec {b : SBlock} {c : SCtor} (h : b.etaCtor? = some c) :
    ∃ t, b.types = [t] ∧ t.indices = [] ∧ b.large = true ∧ t.ctors = [c] ∧
      (∀ f ∈ c.fields, (∃ w, f.cert = .plain w) ∧ mentions b.names f.ty = false) ∧
      (b.level.isNeverZero = true ∨ ∀ i < c.fields.length, c.fieldDep i = false) := by
  unfold SBlock.etaCtor? at h
  split at h
  · rename_i t ht
    split at h
    · rename_i hil
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hil
      split at h
      · rename_i hc
        split at h
        · rename_i hall
          cases h
          simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, Bool.not_eq_true',
            List.any_eq_false, List.mem_range] at hall
          refine ⟨t, ht, hil.1, hil.2, hc, fun f hf => ?_, ?_⟩
          · refine ⟨?_, (hall.1 f hf).2⟩
            have := (hall.1 f hf).1; revert this; cases f.cert <;> simp
          · rcases hall.2 with h | h
            · exact .inl h
            · exact .inr fun i hi => by simpa using h i hi
        · cases h
      · cases h
    · cases h
  · cases h

theorem etaCtor_facts {b : SBlock} {c : SCtor} (h : b.etaCtor? = some c) :
    b.ntypes = 1 ∧ b.nctors = 1 ∧ ctorsOf b 0 = [c] ∧ (b.types[0]!).indices = [] ∧
      b.ctorBase 0 = 0 ∧ c.recFields = [] ∧ b.large = true := by
  obtain ⟨t, ht, hi, hlg, hc, hpl, -⟩ := etaCtor_spec h
  refine ⟨by simp [SBlock.ntypes, ht], by simp [SBlock.nctors, SBlock.ctors, ht, hc],
    by simp [ctorsOf, ht, hc], by simp [ht, hi], by simp [SBlock.ctorBase], ?_, hlg⟩
  unfold SCtor.recFields
  rw [List.filterMap_eq_nil_iff]
  intro a ha
  have ha' : a < c.fields.length := by simpa using ha
  obtain ⟨⟨w, hw⟩, -⟩ := hpl _ (List.getElem_mem ha')
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha']
  simp [hw]

theorem blev_cons {b : SBlock} (hlg : b.large = true) (s : Nat) {ls : List Nat}
    (hl : ls.length = b.uvars) : blev b (s :: ls) = ls := by
  apply List.ext_getElem (by simp [blev, SBlock.blockLevels, hl])
  intro i h1 h2
  simp [blev, SBlock.blockLevels, hlg, VLevel.eval, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem h2]; rfl

theorem interp_place_nodep {M' : CInterp V} {ls' : List Nat} {b : SBlock} {c : SCtor} {i : Nat}
    (hnd : c.fieldDep i = false) (hcl : (c.fields[i]!).ty.ClosedN (b.nparams + i))
    {ps zs : List V} (hp : ps.length = b.nparams) {d : Nat} (hd : b.nparams + zs.length = d) (z : V)
    (ys : List V) (hys : ys.length = i) :
    interp M' ls' (b.place' (b.nparams + i) d (d + 1) (c.fields[i]!).ty)
        ((ps ++ zs ++ [z]).reverse) =
      interp M' ls' (c.fields[i]!).ty (ys.reverse ++ ps.reverse) := by
  unfold SBlock.place' place
  rw [interp_remap M' ls' _ _ (b.nparams + i) _ ((List.range (b.nparams + i)).map fun k =>
      (ps ++ zs ++ [z]).reverse.getD ((d + 1) - 1 - b.σ1 d (b.nparams + i - 1 - k)) pt) hcl
      (fun k hk => by simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk])]
  apply interp_eq_of_agree
  intro j hj
  have hji : i ≤ j := by
    refine Nat.le_of_not_lt fun h => ?_
    have : c.fieldDep i = true := by
      unfold SCtor.fieldDep; exact List.any_eq_true.mpr ⟨j, List.mem_range.mpr (by omega), hj⟩
    simp [hnd] at this
  by_cases hjn : j < b.nparams + i
  · have hσ : b.σ1 d (b.nparams + i - 1 - j) = b.nparams + i - 1 - j := by
      unfold SBlock.σ1; rw [ite_eq_left (by omega)]
    have e1 : (ps ++ zs ++ [z]).reverse = [z] ++ zs.reverse ++ ps.reverse := by simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hjn]
    simp only [Option.map_some, Option.getD_some, hσ, e1]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
    congr 2
    simp; omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]

theorem pull_σ1_take (b : SBlock) {ps mid zs : List V} (hp : ps.length = b.nparams) {D : Nat}
    (hD : ps.length + mid.length = D) (a : Nat) (hz : a ≤ zs.length) :
    ((List.range (b.nparams + a)).map fun L => (ps ++ mid ++ zs).getD (b.σ1 D L) pt) =
      ps ++ zs.take a := by
  rw [← pull_σ1 b hp hD a (zs := zs.take a) (by simp; omega)]
  apply List.map_congr_left
  intro L hL
  have hL' : L < b.nparams + a := by simpa using hL
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  congr 1
  unfold SBlock.σ1
  split
  · rw [List.append_assoc, List.append_assoc, List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega),
      List.getElem?_take_of_lt (by simp; omega)]

theorem scoped_place_any {P : Name → Prop} {d0 d : Nat} {σ : Nat → Nat} {e : VExpr}
    (he : Scoped P d0 e) (hd : 0 < d) : Scoped P d (Spec.place d0 σ d e) := by
  refine ⟨?_, (constsIn_place _ _ _ _).mpr he.2⟩
  have := closedN_remap (fun i => d - 1 - σ (d0 - 1 - i)) (N := d0) (N' := d)
    (fun i _ => by omega) e 0 he.1
  simpa [Spec.place] using this

theorem addEta_le (b : SBlock) (env : VEnv) : env ≤ b.addEta env := by
  unfold SBlock.addEta; split
  · exact VEnv.addDefEq_le
  · exact VEnv.LE.rfl

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem mem_carrier_inv {ls : List Nat} (hl : ls.length = b.uvars) {ps : List V}
    (hps : Ext M ls b.params [] ps) {m : Nat} (hm : m < b.ntypes) {i x : V}
    (hi : i ∈ˢ Is M ls b ps.reverse m)
    (hx : x ∈ˢ app (carrier M ls b ps.reverse m) i) :
    ∃ q c fs, (ctorsOf b m)[q]? = some c ∧
      FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fs ∧
      cidx M ls ps.reverse c fs = i ∧ x = enc ls b q fs := by
  rw [app_carrier S.hK (S.hSmall hl hps) (S.hBound hl hps) hm hi] at hx
  unfold enc
  by_cases h0 : lev ls b = 0
  · obtain ⟨rfl, q, fs, c, hc, hfit, hidx⟩ := (mem_fib_zero h0).mp hx
    exact ⟨q, c, fs, hc, hfit, hidx, by rw [ite_eq_left h0]⟩
  · obtain ⟨q, fs, ⟨c, hc, hfit, hidx⟩, rfl⟩ := (mem_fib_pos h0).mp hx
    exact ⟨q, c, fs, hc, hfit, hidx, by rw [ite_eq_right h0]⟩

end Setting

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S
variable {env₂ env₃ : VEnv} (h2 : addFold env₁ (ctorConsts b) = some env₂)
  (h3 : addFold env₂ (recConsts b) = some env₃)
include h2 h3

theorem type_apps {c : SCtor} (hc : b.etaCtor? = some c) {ls : List Nat}
    {ps : List V} (hps : Ext M ls b.params [] ps) :
    ps.foldl app (M₃ M b (b.types[0]!).name ls) = app (carrier M ls b ps.reverse 0)
        (mkTower []) := by
  obtain ⟨hnt, -, -, hidx, -, -, -⟩ := etaCtor_facts hc
  have hd : 0 < b.ntypes := by omega
  rw [BlockModel.Setting.hag₃₁ h2 h3 _ (S.type_dom hd)]
  have e : (b.types[0]!) = b.types[0]'hd := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hd]; rfl
  unfold Mc
  rw [e, M₁_type S.nodup hd]
  have := apps_former (M := M) (b := b) (C := fun ls ρp => carrier M ls b ρp) (k := 0)
      (is := []) hps
    (by rw [hidx]; exact .nil)
  simpa using this

theorem field_mem_sort {c : SCtor} (hc : b.etaCtor? = some c) {ls : List Nat}
    (hl : ls.length = b.uvars) {ps : List V} (hps : Ext M ls b.params [] ps) {a : Nat}
    (ha : a < c.fields.length) {fs : List V} (hfs : fs.length = a)
    (hfit : FFit M ls (carrier M ls b ps.reverse) (c.fields.take a) ps.reverse fs) :
    interp (M₃ M b) ls (c.fields[a]!).ty (fs.reverse ++ ps.reverse) ∈ˢ
      univ ((c.fields[a]!).sort.eval ls) := by
  obtain ⟨hnt, -, hcs, -, -, -, -⟩ := etaCtor_facts hc
  have hd : 0 < b.ntypes := by omega
  have hcq : (ctorsOf b 0)[0]? = some c := by rw [hcs]; rfl
  have hc' : c ∈ (b.types[0]!).ctors := List.mem_of_getElem? hcq
  have hsat := (S.ffit_iff_sat (carrier_tupleFn M b) hl hd hc' hps a (Nat.le_of_lt ha) fs
      hfs).mp hfit
  obtain ⟨hty, -, -, -⟩ := S.field_ok hd hc' ha
  have hs := ((S.model₁ (carrier_tupleFn M b)).1.sound hty ls _ hsat).2
  have hct : ConstsIn (Dom env₁) (c.fields[a]!).ty :=
    (IsDefEq.constsIn S.good₁.2 hty (S.fctx_consts hd hc' a (Nat.le_of_lt ha))).1
  rw [interp_congr (hct.mono fun x hx => BlockModel.Setting.hag₃₁ h2 h3 x hx)]
  simpa [interp] using hs

theorem rec_struct {c : SCtor} (hc : b.etaCtor? = some c) {ls : List Nat}
    (hl : ls.length = b.recUvars) {ps : List V} (hps : Ext M (blev b ls) b.params [] ps)
        {mot mn : V}
    (hmot : mot ∈ˢ interp (M₃ M b) ls (b.motiveTy 0) ps.reverse)
    (hmn : mn ∈ˢ interp (M₃ M b) ls (b.minorTy 0 c (b.nparams + 1)) (mot :: ps.reverse))
    {fs : List V} (hfit : FFit M (blev b ls) (carrier M (blev b ls) b ps.reverse) c.fields
        ps.reverse fs) :
    (ps ++ [mot, mn, enc (blev b ls) b 0 fs]).foldl app
        (M₃ M b (b.recName 0) (b.recLevels.map (VLevel.eval ls))) = fs.foldl app mn ∧
      fs.foldl app mn ∈ˢ app mot (enc (blev b ls) b 0 fs) := by
  obtain ⟨hnt, hnc, hcs, hidx, hcb, hrf, hlg⟩ := etaCtor_facts hc
  obtain ⟨t, ht, hti, -, htc, -, -⟩ := etaCtor_spec hc
  have hcq : (ctorsOf b 0)[0]? = some c := by rw [hcs]; rfl
  have hd : 0 < b.ntypes := by omega
  have hc' : c ∈ (b.types[0]!).ctors := List.mem_of_getElem? hcq
  have hag := BlockModel.Setting.hag₃₁ (M := M) h2 h3
  have hM3 := S.model₃₁ h2 h3
  have hlb := blev_length b ls
  have hP := (S.ext_params hag hM3 ps).mpr hps
  have hT : Ext (M₃ M b) ls ((List.range b.ntypes).map b.motiveTy) (ps.reverse ++ []) [mot] := by
    rw [hnt]; exact .cons (by simpa using hmot) .nil
  have hml : minorList b = [b.minorTy 0 c (b.nparams + 1)] := by
    unfold minorList
    rw [hnt]
    simp [ht, htc, hcb]
  have hN : Ext (M₃ M b) ls (minorList b) ((ps ++ [mot]).reverse ++ []) [mn] := by
    rw [hml]; exact .cons (by simpa using hmn) .nil
  obtain ⟨-, hmotl, hminl, hMot, hMin⟩ := S.pre_facts hag hM3
      (BlockModel.Setting.hctor₃ h2 h3) hP hT hN
  have hpre : Ext (M₃ M b) ls b.preTel [] (ps ++ [mot] ++ [mn]) := by
    rw [preTel_eq]
    exact Ext.append (Ext.append hP (by simpa using hT)) (by simpa using hN)
  let iv := c.idx.map (interp M (blev b ls) · (fs.reverse ++ ps.reverse))
  have hiv : Ext M (blev b ls) (b.types[0]!).indices ps.reverse iv := S.ctor_result hlb hcq hps hfit
  have hiv0 : iv = [] := by
    have := Ext.length_eq M _ hiv; rw [hidx] at this; simpa using this
  have hK := S.hK
  have hs := S.hSmall hlb hps
  have hB := S.hBound hlb hps
  have hi : mkTower iv ∈ˢ Is M (blev b ls) b ps.reverse 0 := mkTower_mem_extSet M _ hiv
  have henc := enc_mem hK hs hB hd hcq hfit hi
  have hu : tagged 0 (mkTower iv) (enc (blev b ls) b 0 fs) ∈ˢ U M (blev b ls) b ps.reverse :=
    mem_unionSet.mpr ⟨0, hd, _, hi, _, henc, rfl⟩
  have hdec : Dec M (blev b ls) b ps.reverse (tagged 0 (mkTower iv) (enc (blev b ls) b 0 fs))
      (0, 0, fs) :=
    ⟨mkTower iv, hi, ⟨c, hcq, hfit, rfl⟩, rfl⟩
  have huq : elimLev b ls ≠ 0 → lev (blev b ls) b = 0 → HUniq M (blev b ls) b ps.reverse :=
    fun _ h0 => S.hUniq hlb hps h0 hlg
  have hcall := S.rec_call_eq h2 h3 hl hpre hps hmotl hminl hd hiv henc
  rw [hiv0] at hcall
  simp only [List.append_nil] at hcall
  have hstep := rec_eq hK hs hB hMot hMin huq hu hdec
  have hrec := rec_mem hK hs hB hMot hMin huq hu
  rw [hiv0] at hstep hrec
  unfold st at hstep
  simp only [hcq, hrf, List.map_nil, List.append_nil, hcb] at hstep
  unfold Bnd at hrec
  rw [untag_tagged] at hrec
  simp only [] at hrec
  rw [projList_mkTower _ _ (by simp [nidx, ht, hti])] at hrec
  simp only [List.foldl_nil, List.getD_cons_zero] at hrec
  have e : ps ++ [mot, mn, enc (blev b ls) b 0 fs] = ps ++ [mot] ++ [mn] ++
      [enc (blev b ls) b 0 fs] := by
    simp
  rw [e, hcall, hstep]
  rw [hstep] at hrec
  exact ⟨by simp, by simpa using hrec⟩

theorem rec_val_core {c : SCtor} (hc : b.etaCtor? = some c) {ls : List Nat}
    (hl : ls.length = b.uvars)
    {ps zs : List V} (hps : Ext M ls b.params [] ps) {d : Nat} (hd : b.nparams + zs.length = d)
    (lv : VLevel) (mot : V) (h : List V → V) {fs : List V}
    (hfit : FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fs)
    (hmotS : mot ∈ˢ cpi (app (carrier M ls b ps.reverse 0) (mkTower [])) fun _ => univ (lv.eval ls))
    (hH : ∀ fs', FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fs' →
      h (ps ++ zs ++ fs').reverse ∈ˢ app mot (enc ls b 0 fs')) :
    (ps ++ [mot, Soulgem.lamTel (M₃ M b) ls (b.etaFields c d) h (ps ++ zs).reverse,
        enc ls b 0 fs]).foldl
      app (M₃ M b (b.recName 0) (lv.eval ls :: ls)) = h (ps ++ zs ++ fs).reverse := by
  obtain ⟨hnt, -, hcs, hidx, -, hrf, hlg⟩ := etaCtor_facts hc
  have hcq : (ctorsOf b 0)[0]? = some c := by rw [hcs]; rfl
  have hd0 : 0 < b.ntypes := by omega
  have hc' : c ∈ (b.types[0]!).ctors := List.mem_of_getElem? hcq
  have hag := BlockModel.Setting.hag₃₁ (M := M) h2 h3
  have hM3 := S.model₃₁ h2 h3
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hl' : (lv.eval ls :: ls).length = b.recUvars := by simp [SBlock.recUvars, hlg, hl]
  have hb : blev b (lv.eval ls :: ls) = ls := blev_cons hlg _ hl
  have hcidx : c.idx = [] := by
    have := Ext.length_eq M _ (S.ctor_result hl hcq hps hfit)
    rw [hidx] at this; simpa using this
  have hpsc : Ext (Mc M b) ls b.params [] ps :=
    (Ext.congrM (M := M) (M' := Mc M b) (fun _ h => h) fun A hA =>
      (S.free₀ (S.params_consts' A hA)).mono fun _ h => h.symm).mp hps
  have hpsM : Ext (M₃ M b) ls b.params [] ps :=
    (Ext.congrM (fun x h => h) fun A hA => ((S.free₀ (C := fun ls ρp => carrier M ls b ρp)
      (S.params_consts' A hA)).and ((S.params_consts' A hA).mono fun _ => Dom.mono S.le₁)).mono
        fun x ⟨h1, h2⟩ => h1.symm.trans (hag x h2).symm).mp hps
  have hpS : Sat (M₃ M b) (blev b (lv.eval ls :: ls)) b.params.reverse ps.reverse := by
    rw [hb]; simpa using Sat.of_ext (Γ := []) (ρ := []) trivial hpsM
  have hext : ∀ xs, FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse xs ↔
      Ext (M₃ M b) ls (c.fields.map (·.ty)) ps.reverse xs := by
    intro xs
    constructor
    · intro hx
      have hxl : xs.length = c.fields.length := by
        have := FFit.length_eq (M := M) (ls := ls) hx; simpa using this
      have hsat := (S.ffit_iff_sat (carrier_tupleFn M b) hl hd0 hc' hps c.fields.length
        (Nat.le_refl _) xs hxl).mp (by simpa using hx)
      have hsat3 := (Sat.congrM' (M' := Mc M b) (fun x hx => hag x hx)
        (S.fctx_consts hd0 hc' c.fields.length (Nat.le_refl _))).mpr hsat
      have e : fctx b c c.fields.length = (c.fields.map (·.ty)).reverse ++ b.params.reverse := by
        simp [fctx]
      rw [e] at hsat3
      exact (Ext.of_sat (by simp [hxl]) hsat3).2
    · intro hx
      have hpS' : Sat (M₃ M b) ls b.params.reverse ps.reverse := by rwa [hb] at hpS
      have hsat3 : Sat (M₃ M b) ls (fctx b c c.fields.length) (xs.reverse ++ ps.reverse) := by
        have := Sat.of_ext hpS' hx; simpa [fctx] using this
      have hsatc := (Sat.congrM' (M' := Mc M b) (fun x hx => hag x hx)
        (S.fctx_consts hd0 hc' c.fields.length (Nat.le_refl _))).mp hsat3
      have hxl : xs.length = c.fields.length := by rw [Ext.length_eq _ _ hx]; simp
      have := (S.ffit_iff_sat (carrier_tupleFn M b) hl hd0 hc' hps c.fields.length
          (Nat.le_refl _) xs
        hxl).mpr hsatc
      simpa using this
  have hmot : mot ∈ˢ interp (M₃ M b) (lv.eval ls :: ls) (b.motiveTy 0) ps.reverse := by
    have e : interp (M₃ M b) (lv.eval ls :: ls) (b.motiveTy 0) ps.reverse =
        cpi (app (carrier M ls b ps.reverse 0) (mkTower [])) fun _ => univ (lv.eval ls) := by
      have hmaj : interp (M₃ M b) (lv.eval ls :: ls) (appN (b.tconst 0)
          (vars b.nparams 0 b.nparams ++ vars b.nparams b.nparams 0)) ps.reverse =
          app (carrier M ls b ps.reverse 0) (mkTower []) := by
        rw [interp_appN, List.map_append, interp_vars _ _ (xs := ps) hplen (by omega),
          interp_vars _ _ (xs := ps) hplen (by omega)]
        simp only [List.drop_zero, List.take_zero,
          List.append_nil, SBlock.tconst]
        rw [show interp (M₃ M b) (lv.eval ls :: ls) (.const (b.types[0]!).name b.blockLevels)
            ps.reverse =
          M₃ M b (b.types[0]!).name ls from by simp only [interp]; rw [show b.blockLevels.map
            (VLevel.eval (lv.eval ls :: ls)) = ls from hb]]
        rw [List.take_of_length_le (by omega)]
        exact S.type_apps h2 h3 hc hps
      unfold SBlock.motiveTy
      simp only [hidx, List.length_nil, List.range_zero, List.map_nil, Nat.add_zero, Spec.forallTel]
      change cpi (interp (M₃ M b) _ (appN (b.tconst 0) _) ps.reverse)
        (fun x => interp (M₃ M b) _ b.elimSort (x :: ps.reverse)) = _
      rw [hmaj]
      congr 1
      funext _
      rw [interp_elimSort]; simp [elimLev, hlg]
    rw [e]; exact hmotS
  let Bs := (List.range c.fields.length).map fun a =>
    b.binder (place (b.nparams + a) (b.σ1 (b.nparams + 1)) (b.nparams + 1 + a) (c.fields[a]!).ty)
  have hBext : ∀ xs, Ext (M₃ M b) (lv.eval ls :: ls) Bs (ps ++ [mot]).reverse xs ↔
      Ext (M₃ M b) ls (c.fields.map (·.ty)) ps.reverse xs := by
    intro xs
    have := S.ext_fields hM3 hplen hd0 hc' (mid := [mot]) (D := b.nparams + 1)
        (by simp [hplen]) hpS xs
    rw [hb] at this; exact this
  obtain ⟨mn, hmnv⟩ : ∃ m, m = Soulgem.lamTel (M₃ M b) ls (b.etaFields c d) h
      (ps ++ zs).reverse :=
    ⟨_, rfl⟩
  have hmnEq : mn = Soulgem.lamTel (M₃ M b) (lv.eval ls :: ls) Bs
      (fun ρ' => h (ρ'.take c.fields.length ++ (ps ++ zs).reverse)) (mot :: ps.reverse) := by
    rw [hmnv]
    refine lamTel_transfer (by simp [SBlock.etaFields, Bs]) (fun a h h' ys hys => ?_)
        (fun ys hys => ?_)
    · have ha : a < c.fields.length := by simpa [Bs] using h'
      have hya : ys.length = a := by
        rw [Ext.length_eq _ _ hys, List.length_take]; simp [Bs]; omega
      simp only [SBlock.etaFields, Bs, List.getElem_map, List.getElem_range,
          SBlock.binder, SBlock.sh,
        consumeAnn_instL, consumeAnn_place, SBlock.place', interp_instL, hb]
      have hcl := closedN_consumeAnn _
        (S.field_scoped (P := fun _ => True) (fun _ _ => trivial) hd0 hc' ha).1
      rw [show ys.reverse ++ (ps ++ zs).reverse = (ps ++ zs ++ ys).reverse by simp,
        show ys.reverse ++ mot :: ps.reverse = (ps ++ [mot] ++ ys).reverse by simp,
        interp_place _ _ _ _ _ _ _ hcl (by simp [hplen, hya]; omega)
          (fun L hL => by unfold SBlock.σ1; split <;> omega),
        interp_place _ _ _ _ _ _ _ hcl (by simp [hplen, hya]; omega)
          (fun L hL => by unfold SBlock.σ1; split <;> omega),
        pull_σ1 b hplen (mid := zs) (by omega) a hya, pull_σ1 b hplen (mid := [mot])
            (by simp [hplen]) a hya]
    · have hyl : ys.length = c.fields.length := by rw [Ext.length_eq _ _ hys]; simp [Bs]
      rw [List.take_append_of_le_length (by simp [hyl]), List.take_of_length_le (by simp [hyl])]
  have hmn : mn ∈ˢ interp (M₃ M b) (lv.eval ls :: ls) (b.minorTy 0 c (b.nparams + 1))
      (mot :: ps.reverse) := by
    have e : b.minorTy 0 c (b.nparams + 1) = Spec.forallTel Bs (.app (var (b.nparams + 1 +
        c.fields.length) b.nparams) (appN (.const c.name b.blockLevels)
          (vars (b.nparams + 1 + c.fields.length) 0 b.nparams ++
            vars (b.nparams + 1 + c.fields.length) (b.nparams + 1) c.fields.length))) := by
      unfold SBlock.minorTy
      simp [hrf, hcidx, Bs, appN]
    rw [e, interp_forallTel, hmnEq]
    refine lamTel_mem_piTel fun xs hxs => ?_
    have hxl : xs.length = c.fields.length := by rw [Ext.length_eq _ _ hxs]; simp [Bs]
    have hxE := (hBext xs).mp (by simpa using hxs)
    have hx := (hext xs).mpr hxE
    have hW : (ps ++ [mot] ++ xs).length = b.nparams + 1 + c.fields.length := by
      simp [hplen, hxl]; omega
    have hrv : xs.reverse ++ mot :: ps.reverse = (ps ++ [mot] ++ xs).reverse := by simp
    rw [List.take_append_of_le_length (by simp [hxl]), List.take_of_length_le (by simp [hxl]), hrv]
    simp only [interp]
    rw [interp_var _ _ hW (by omega), interp_appN, List.map_append, interp_vars _ _ hW (by omega),
      interp_vars _ _ hW (by omega)]
    have e0 : ((ps ++ [mot] ++ xs).drop 0).take b.nparams = ps := by simp [hplen]
    have eD : ((ps ++ [mot] ++ xs).drop (b.nparams + 1)).take c.fields.length = xs := by
      rw [show b.nparams + 1 = (ps ++ [mot]).length by simp [hplen], List.drop_left, ← hxl,
        List.take_length]
    have em : (ps ++ [mot] ++ xs).getD b.nparams pt = mot := by
      rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega)]
      simp [hplen]
    rw [e0, eD, em]
    simp only [interp, BlockModel.Setting.hctor₃ h2 h3 0 hd0 0 c hcq, hb]
    have hfsc : Ext (Mc M b) ls (c.fields.map (·.ty)) ps.reverse xs := by
      refine (Ext.congrM (M := M₃ M b) (M' := Mc M b) (fun x hx => hag x hx) fun A hA => ?_).mp hxE
      exact S.fctx_consts hd0 hc' c.fields.length (Nat.le_refl _) A
        (by simp only [fctx, List.take_length, List.mem_reverse, List.mem_append]; exact .inr hA)
    have hintro : (ps ++ xs).foldl app (ctorVal b (Mc M b) ls 0 c) = enc ls b 0 xs := by
      unfold ctorVal
      rw [List.foldl_append, apps_lamTel hpsc]
      simp only [List.append_nil]
      rw [apps_lamTel hfsc]
      have htk : (xs.reverse ++ ps.reverse).take c.fields.length = xs.reverse :=
        (List.take_append_of_le_length (by simp [hxl])).trans (List.take_of_length_le
            (by simp [hxl]))
      rw [htk, List.reverse_reverse]
    rw [hintro]
    have := hH xs hx
    simpa using this
  have hfE := (hext fs).mp hfit
  have hfsB := (hBext fs).mpr hfE
  obtain ⟨h1, -⟩ := S.rec_struct h2 h3 hc hl' (by rw [hb]; exact hps) hmot hmn
    (by rw [hb]; exact hfit)
  rw [hb, recLevels_eval _ hl'] at h1
  have hval : fs.foldl app mn = h (ps ++ zs ++ fs).reverse := by
    rw [hmnEq, apps_lamTel (by simpa using hfsB)]
    have hfl : fs.length = c.fields.length := by rw [Ext.length_eq _ _ hfE]; simp
    rw [List.take_append_of_le_length (by simp [hfl]), List.take_of_length_le (by simp [hfl])]
    simp
  rw [← hmnv]
  exact h1.trans hval

theorem rec_val {c : SCtor} (hc : b.etaCtor? = some c) {ls : List Nat} (hl : ls.length = b.uvars)
    {ps zs : List V} (hps : Ext M ls b.params [] ps) {d : Nat} (hd : b.nparams + zs.length = d)
    (lv : VLevel) (G H y : VExpr) {fs : List V}
    (hfit : FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fs)
    (hy : interp (M₃ M b) ls y (ps ++ zs).reverse = enc ls b 0 fs)
    (hG : ∀ z, z ∈ˢ app (carrier M ls b ps.reverse 0) (mkTower []) →
      interp (M₃ M b) ls G (z :: (ps ++ zs).reverse) ∈ˢ univ (lv.eval ls))
    (hH : ∀ fs', FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fs' →
      interp (M₃ M b) ls H (ps ++ zs ++ fs').reverse ∈ˢ
        interp (M₃ M b) ls G (enc ls b 0 fs' :: (ps ++ zs).reverse)) :
    interp (M₃ M b) ls (appN (.const (b.recName 0) (lv :: ownLevels b.uvars))
        (vars d 0 b.nparams ++ [.lam (appN (.const (b.types[0]!).name (ownLevels b.uvars))
          (vars d 0 b.nparams)) G, Spec.lamTel (b.etaFields c d) H, y])) (ps ++ zs).reverse =
      interp (M₃ M b) ls H (ps ++ zs ++ fs).reverse ∧
    interp (M₃ M b) ls H (ps ++ zs ++ fs).reverse ∈ˢ
      interp (M₃ M b) ls G (enc ls b 0 fs :: (ps ++ zs).reverse) := by
  obtain ⟨hnt, -, hcs, hidx, -, hrf, hlg⟩ := etaCtor_facts hc
  have hcq : (ctorsOf b 0)[0]? = some c := by rw [hcs]; rfl
  have hd0 : 0 < b.ntypes := by omega
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hown := ownLevels_eval (b := b) hl
  have hcidx : c.idx = [] := by
    have := Ext.length_eq M _ (S.ctor_result hl hcq hps hfit)
    rw [hidx] at this; simpa using this
  have hvars : ∀ (xs : List V) (D : Nat), (ps ++ xs).length = D →
      (vars D 0 b.nparams).map (interp (M₃ M b) ls · (ps ++ xs).reverse) = ps := by
    intro xs D hD
    rw [interp_vars _ _ hD (by simp [← hD, hplen])]; simp [hplen]
  have hSv : interp (M₃ M b) ls (appN (.const (b.types[0]!).name (ownLevels b.uvars))
      (vars d 0 b.nparams)) (ps ++ zs).reverse = app (carrier M ls b ps.reverse 0)
          (mkTower []) := by
    rw [interp_appN, hvars zs d (by simp [hplen]; omega)]
    simp only [interp, hown]
    exact S.type_apps h2 h3 hc hps
  have henc : ∀ xs, FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse xs →
      enc ls b 0 xs ∈ˢ app (carrier M ls b ps.reverse 0) (mkTower []) := by
    intro xs hx
    have hi : cidx M ls ps.reverse c xs ∈ˢ Is M ls b ps.reverse 0 :=
      mkTower_mem_extSet M _ (S.ctor_result hl hcq hps hx)
    have := enc_mem S.hK (S.hSmall hl hps) (S.hBound hl hps) hd0 hcq hx hi
    simpa [cidx, hcidx] using this
  obtain ⟨mot, hmotv⟩ : ∃ m, m = interp (M₃ M b) ls (.lam (appN (.const (b.types[0]!).name
      (ownLevels b.uvars)) (vars d 0 b.nparams)) G) (ps ++ zs).reverse := ⟨_, rfl⟩
  have happ : ∀ xs, FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse xs →
      app mot (enc ls b 0 xs) = interp (M₃ M b) ls G (enc ls b 0 xs :: (ps ++ zs).reverse) := by
    intro xs hx
    rw [hmotv]; simp only [interp]
    rw [hSv, app_clam (henc xs hx)]
  have hmotS : mot ∈ˢ cpi (app (carrier M ls b ps.reverse 0) (mkTower [])) fun _ =>
      univ (lv.eval ls) := by
    rw [hmotv]; simp only [interp]; rw [hSv]; exact clam_mem_cpi fun z hz => hG z hz
  have hcore := S.rec_val_core h2 h3 hc hl hps hd lv mot (interp (M₃ M b) ls H) hfit hmotS
    fun fs' hf => by rw [happ fs' hf]; exact hH fs' hf
  rw [interp_appN, List.map_append, hvars zs d (by simp [hplen]; omega)]
  simp only [List.map_cons, List.map_nil]
  rw [← hmotv, interp_lamTel', hy]
  rw [show interp (M₃ M b) ls (.const (b.recName 0) (lv :: ownLevels b.uvars)) (ps ++ zs).reverse =
    M₃ M b (b.recName 0) (lv.eval ls :: ls) from by simp only [interp, List.map_cons, hown]]
  rw [hcore]
  exact ⟨rfl, hH fs hfit⟩

theorem ffit_ext {c : SCtor} (hc : b.etaCtor? = some c) {ls : List Nat} (hl : ls.length = b.uvars)
    {ps : List V} (hps : Ext M ls b.params [] ps) {xs : List V}
    (hx : FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse xs) :
    Ext (M₃ M b) ls (c.fields.map (·.ty)) ps.reverse xs := by
  obtain ⟨hnt, -, hcs, -, -, -, -⟩ := etaCtor_facts hc
  have hcq : (ctorsOf b 0)[0]? = some c := by rw [hcs]; rfl
  have hd0 : 0 < b.ntypes := by omega
  have hc' : c ∈ (b.types[0]!).ctors := List.mem_of_getElem? hcq
  have hxl : xs.length = c.fields.length := by
    have := FFit.length_eq (M := M) (ls := ls) hx; simpa using this
  have hsat := (S.ffit_iff_sat (carrier_tupleFn M b) hl hd0 hc' hps c.fields.length
    (Nat.le_refl _) xs hxl).mp (by simpa using hx)
  have hsat3 := (Sat.congrM' (M' := Mc M b) (fun x hx => BlockModel.Setting.hag₃₁ h2 h3 x hx)
    (S.fctx_consts hd0 hc' c.fields.length (Nat.le_refl _))).mpr hsat
  have e : fctx b c c.fields.length = (c.fields.map (·.ty)).reverse ++ b.params.reverse := by
    simp [fctx]
  rw [e] at hsat3
  exact (Ext.of_sat (by simp [hxl]) hsat3).2

theorem proj_val' {c : SCtor} (hc : b.etaCtor? = some c) {ls : List Nat} (hl : ls.length = b.uvars)
    {ps : List V} (hps : Ext M ls b.params [] ps) (i : Nat) :
    ∀ {d : Nat} {zs fs : List V}, b.nparams + zs.length = d →
    FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fs → i < c.fields.length →
    interp (M₃ M b) ls (b.projV c (d + 1) (var (d + 1) d) i)
      (ps ++ zs ++ [enc ls b 0 fs]).reverse = fs.getD i pt := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro d zs fs hd hfit hi
  obtain ⟨hnt, -, hcs, hidx, -, -, hlg⟩ := etaCtor_facts hc
  have hcq : (ctorsOf b 0)[0]? = some c := by rw [hcs]; rfl
  have hd0 : 0 < b.ntypes := by omega
  have hc' : c ∈ (b.types[0]!).ctors := List.mem_of_getElem? hcq
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hfl : fs.length = c.fields.length := by
    have := FFit.length_eq (M := M) (ls := ls) hfit; simpa using this
  have hcl := (S.field_scoped (P := fun _ => True) (fun _ _ => trivial) hd0 hc' hi).1
  have hlast : ∀ (xs : List V) (x : V), (xs ++ [x]).getD xs.length pt = x := fun xs x => by
    simp [List.getD_eq_getElem?_getD]
  let nf := c.fields.length
  let ty := (c.fields[i]!).ty
  let g : Nat → VExpr := fun j => if h : j < i then
      have : i - 1 - j < i := by omega
      b.projV c (d + 1 + 1) (var (d + 1 + 1) (d + 1)) (i - 1 - j)
    else var (d + 1 + 1) (b.nparams - 1 - (j - i))
  let F := if !c.fieldDep i then b.place' (b.nparams + i) (d + 1) (d + 1 + 1) ty
    else if b.level.isNeverZero && !c.substField i then
      b.etaFieldTy c (d + 1 + 1) (var (d + 1 + 1) (d + 1)) i
    else subst g ty
  have hproj : b.projV c (d + 1) (var (d + 1) d) i =
      appN (.const (b.recName 0) ((c.fields[i]!).sort :: ownLevels b.uvars))
        (vars (d + 1) 0 b.nparams ++ [.lam (appN (.const (b.types[0]!).name (ownLevels b.uvars))
          (vars (d + 1) 0 b.nparams)) F, Spec.lamTel (b.etaFields c (d + 1))
              (var (d + 1 + nf) (d + 1 + i)),
          var (d + 1) d]) := by
    rw [SBlock.projV]; simp only [hlg, ite_true, Bool.true_and]; rfl
  have hFval : ∀ fz, FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fz →
      interp (M₃ M b) ls F (enc ls b 0 fz :: (ps ++ (zs ++ [enc ls b 0 fs])).reverse) =
        interp (M₃ M b) ls ty ((fz.take i).reverse ++ ps.reverse) ∧
      interp (M₃ M b) ls ty ((fz.take i).reverse ++ ps.reverse) ∈ˢ
        univ ((c.fields[i]!).sort.eval ls) := by
    intro fz hfz
    have hfzl : fz.length = c.fields.length := by
      have := FFit.length_eq (M := M) (ls := ls) hfz; simpa using this
    have hpre : FFit M ls (carrier M ls b ps.reverse) (c.fields.take i) ps.reverse (fz.take i) := by
      have e : c.fields = c.fields.take i ++ c.fields.drop i := (List.take_append_drop _ _).symm
      rw [e, ← List.take_append_drop i fz] at hfz
      exact ((FFit.append (by simp; omega)).mp hfz).1
    have hmem := S.field_mem_sort h2 h3 hc hl hps hi (fs := fz.take i) (by simp; omega) hpre
    refine ⟨?_, hmem⟩
    have hrv : enc ls b 0 fz :: (ps ++ (zs ++ [enc ls b 0 fs])).reverse =
        (ps ++ (zs ++ [enc ls b 0 fs, enc ls b 0 fz])).reverse := by simp
    by_cases hdep : c.fieldDep i
    · by_cases heta : (b.level.isNeverZero && !c.substField i) = true
      ·
        have hF : F = b.etaFieldTy c (d + 1 + 1) (var (d + 1 + 1) (d + 1)) i := by
          simp only [F, hdep, heta]; rfl
        have hHval : ∀ zf, zf.length = c.fields.length →
            interp (M₃ M b) ls (b.place' (b.nparams + i) (d + 1 + 1) (d + 1 + 1 + nf) ty)
              (ps ++ (zs ++ [enc ls b 0 fs, enc ls b 0 fz]) ++ zf).reverse =
            interp (M₃ M b) ls ty ((zf.take i).reverse ++ ps.reverse) := by
          intro zf hzf
          unfold SBlock.place'
          rw [interp_place _ _ _ _ _ _ _ hcl (by simp [hplen, hzf, nf]; omega)
              (fun L hL => by unfold SBlock.σ1; split <;> omega),
            pull_σ1_take b hplen (mid := zs ++ [enc ls b 0 fs, enc ls b 0 fz])
                (by simp [hplen]; omega) i
              (by omega), List.reverse_append]
        have hval := S.rec_val h2 h3 hc hl hps (zs := zs ++ [enc ls b 0 fs, enc ls b 0 fz])
            (d := d + 1 + 1)
          (by simp; omega) (.succ (c.fields[i]!).sort) (.sort (c.fields[i]!).sort)
          (b.place' (b.nparams + i) (d + 1 + 1) (d + 1 + 1 + nf) ty) (var (d + 1 + 1) (d + 1)) hfz
          (by
              rw [show ps ++ (zs ++ [enc ls b 0 fs, enc ls b 0 fz]) = ps ++ zs ++ [enc ls b 0 fs] ++
                  [enc ls b 0 fz] by simp,
                interp_var _ _ (by
                    simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                  (by omega),
                show d + 1 = (ps ++ zs ++ [enc ls b 0 fs]).length by
                  simp only [List.length_append, List.length_cons, List.length_nil]; omega]
              exact hlast _ _)
          (fun z _ => by simp only [interp, VLevel.eval]; exact univ_mem_univ _)
          (fun zf hzf => by
            have hzl : zf.length = c.fields.length := by
              have := FFit.length_eq (M := M) (ls := ls) hzf; simpa using this
            rw [hHval zf hzl]
            simp only [interp]
            have hpre' : FFit M ls (carrier M ls b ps.reverse) (c.fields.take i) ps.reverse
                (zf.take i) := by
              have e : c.fields = c.fields.take i ++ c.fields.drop i :=
                  (List.take_append_drop _ _).symm
              rw [e, ← List.take_append_drop i zf] at hzf
              exact ((FFit.append (by simp; omega)).mp hzf).1
            exact S.field_mem_sort h2 h3 hc hl hps hi (by simp; omega) hpre')
        have e : (b.etaFieldTy c (d + 1 + 1) (var (d + 1 + 1) (d + 1)) i) =
            appN (.const (b.recName 0) (.succ (c.fields[i]!).sort :: ownLevels b.uvars))
              (vars (d + 1 + 1) 0 b.nparams ++ [.lam (appN (.const (b.types[0]!).name
                  (ownLevels b.uvars))
                (vars (d + 1 + 1) 0 b.nparams)) (.sort (c.fields[i]!).sort),
                Spec.lamTel (b.etaFields c (d + 1 + 1)) (b.place' (b.nparams + i) (d + 1 + 1)
                    (d + 1 + 1 + nf) ty),
                var (d + 1 + 1) (d + 1)]) := by
          simp [SBlock.etaFieldTy, nf, ty]
        rw [hF, e, hrv, hval.1, hHval fz hfzl]
      ·
        have hF : F = subst g ty := by
          simp only [F, hdep, heta]; rfl
        rw [hF, hrv]
        have hsub := interp_subst (M₃ M b) ls g ty 0 (b.nparams + i) []
            (ps ++ (zs ++ [enc ls b 0 fs, enc ls b 0 fz])).reverse
          ((fz.take i).reverse ++ ps.reverse) (by rw [Nat.zero_add]; exact hcl) rfl (fun j hj => ?_)
        · simpa using hsub
        by_cases hji : j < i
        · have hih := ih (i - 1 - j) (by omega) (d := d + 1) (zs := zs ++
            [enc ls b 0 fs]) (fs := fz)
            (by simp; omega) hfz (by omega)
          simp only [g, dite_eq_left hji]
          rw [show ps ++ (zs ++ [enc ls b 0 fs, enc ls b 0 fz]) = ps ++ (zs ++ [enc ls b 0 fs]) ++
              [enc ls b 0 fz] by simp, hih,
            getD_append_lt (l₁ := (fz.take i).reverse) (by simp; omega),
            getD_reverse (xs := fz.take i) (by simp; omega)]
          simp only [List.length_take, hfzl, Nat.min_eq_left (Nat.le_of_lt hi),
              List.getD_eq_getElem?_getD]
          rw [List.getElem?_take_of_lt (by omega)]
        · simp only [g, dite_eq_right hji]
          rw [interp_var _ _ (xs := ps ++ (zs ++ [enc ls b 0 fs, enc ls b 0 fz]))
              (by simp [hplen]; omega) (by omega),
            getD_append_ge (l₁ := (fz.take i).reverse) (by simp; omega),
            getD_append_lt (l₁ := ps) (by omega), getD_reverse (xs := ps) (by simp; omega)]
          simp only [List.length_take, List.length_reverse, hfzl,
              Nat.min_eq_left (Nat.le_of_lt hi), hplen]
    · have hnd : c.fieldDep i = false := by simpa using hdep
      have hF : F = b.place' (b.nparams + i) (d + 1) (d + 1 + 1) ty := by
        simp only [F, hnd]; rfl
      rw [hF, show enc ls b 0 fz :: (ps ++ (zs ++ [enc ls b 0 fs])).reverse =
          (ps ++ (zs ++ [enc ls b 0 fs]) ++ [enc ls b 0 fz]).reverse by simp]
      exact interp_place_nodep hnd hcl hplen (zs := zs ++ [enc ls b 0 fs]) (by simp; omega) _ _
        (by simp; omega)
  have hval := S.rec_val h2 h3 hc hl hps (zs := zs ++ [enc ls b 0 fs]) (d := d + 1) (by simp; omega)
    (c.fields[i]!).sort F (var (d + 1 + nf) (d + 1 + i)) (var (d + 1) d) hfit
    (by rw [← List.append_assoc,
          interp_var _ _ (by
              simp only [List.length_append, List.length_cons, List.length_nil]; omega)
            (by omega),
          show d = (ps ++ zs).length by simp only [List.length_append]; omega]
        exact hlast _ _)
    (fun z hz => by
      have hi0 : mkTower [] ∈ˢ Is M ls b ps.reverse 0 :=
        mkTower_mem_extSet M _ (by
            rw [hidx]; exact .nil : Ext M ls (b.types[0]!).indices ps.reverse [])
      obtain ⟨q, c', fz, hq, hfz, -, rfl⟩ := S.mem_carrier_inv hl hps hd0 hi0 hz
      have hq0 : q = 0 ∧ c' = c := by
        rw [hcs] at hq
        cases q with
        | zero => simp at hq; exact ⟨rfl, hq.symm⟩
        | succ q => simp at hq
      obtain ⟨rfl, rfl⟩ := hq0
      rw [(hFval fz hfz).1]; exact (hFval fz hfz).2)
    (fun fz hfz => by
      have hfzl : fz.length = c.fields.length := by
        have := FFit.length_eq (M := M) (ls := ls) hfz; simpa using this
      rw [interp_var _ _ (xs := ps ++ (zs ++ [enc ls b 0 fs]) ++ fz)
          (by simp [hplen, hfzl, nf]; omega)
        (by omega), (hFval fz hfz).1]
      have hE := (S.ffit_ext h2 h3 hc hl hps hfz).get i (by simpa using hi) (by omega)
      have e1 : (ps ++ (zs ++ [enc ls b 0 fs]) ++ fz).getD (d + 1 + i) pt = fz[i] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hplen]; omega)]
        simp only [List.length_append, List.length_cons, List.length_nil, hplen]
        rw [show d + 1 + i - (b.nparams + (zs.length + (0 + 1))) = i by omega,
          List.getElem?_eq_getElem (show i < fz.length by omega)]
        rfl
      have e2 : (c.fields.map (·.ty))[i]'(by simpa using hi) = ty := by
        simp [ty, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rw [e1]; rw [e2] at hE; exact hE)
  rw [hproj, List.append_assoc, hval.1]
  rw [interp_var _ _ (xs := ps ++ (zs ++ [enc ls b 0 fs]) ++ fs)
      (by simp [hplen, hfl, nf]; omega) (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hplen]; omega),
    List.getD_eq_getElem?_getD]
  simp only [List.length_append, List.length_cons, List.length_nil, hplen]
  rw [show d + 1 + i - (b.nparams + (zs.length + (0 + 1))) = i by omega]

theorem proj_val {c : SCtor} (hc : b.etaCtor? = some c) {ls : List Nat} (hl : ls.length = b.uvars)
    {ps : List V} (hps : Ext M ls b.params [] ps) {fs : List V}
    (hfit : FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fs) {i : Nat}
    (hi : i < c.fields.length) :
    interp (M₃ M b) ls (b.projV c (b.nparams + 1) (var (b.nparams + 1) b.nparams) i)
      (ps ++ [enc ls b 0 fs]).reverse = fs.getD i pt := by
  have := S.proj_val' h2 h3 hc hl hps i (d := b.nparams) (zs := []) (by simp) hfit hi
  simpa using this

theorem eta_core {c : SCtor} (hc : b.etaCtor? = some c) {ls : List Nat} (hl : ls.length = b.uvars)
    {ws : List V} (hws : Ext (M₃ M b) ls (b.params ++
      [appN (.const (b.types[0]!).name (ownLevels b.uvars)) (vars b.nparams 0 b.nparams)]) [] ws) :
    interp (M₃ M b) ls (var (b.nparams + 1) b.nparams) ws.reverse =
      interp (M₃ M b) ls (appN (.const c.name (ownLevels b.uvars))
        (vars (b.nparams + 1) 0 b.nparams ++ (List.range c.fields.length).map
          (b.projV c (b.nparams + 1) (var (b.nparams + 1) b.nparams)))) ws.reverse ∧
    interp (M₃ M b) ls (var (b.nparams + 1) b.nparams) ws.reverse ∈ˢ
      interp (M₃ M b) ls (appN (.const (b.types[0]!).name (ownLevels b.uvars))
        (vars (b.nparams + 1) 0 b.nparams)) ws.reverse := by
  obtain ⟨hnt, -, hcs, hidx, -, -, -⟩ := etaCtor_facts hc
  have hcq : (ctorsOf b 0)[0]? = some c := by rw [hcs]; rfl
  have hd0 : 0 < b.ntypes := by omega
  have hag := BlockModel.Setting.hag₃₁ (M := M) h2 h3
  obtain ⟨ps, xl, rfl, hP, hX⟩ : ∃ ps xl, ws = ps ++ xl ∧
      Ext (M₃ M b) ls b.params [] ps ∧
      Ext (M₃ M b) ls [appN (.const (b.types[0]!).name (ownLevels b.uvars))
        (vars b.nparams 0 b.nparams)] (ps.reverse ++ []) xl := by
    have h := BlockModel.Ext.split hws
    exact ⟨_, _, (List.take_append_drop _ _).symm, h.1, h.2⟩
  obtain ⟨x, hx⟩ : ∃ x, xl = [x] := by
    have := Ext.length_eq _ _ hX
    match xl, this with
    | [x], _ => exact ⟨x, rfl⟩
  subst hx
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq _ _ hP]; rfl
  have hps : Ext M ls b.params [] ps :=
    (Ext.congrM (fun x h => h) fun A hA => ((S.free₀ (C := fun ls ρp => carrier M ls b ρp)
      (S.params_consts' A hA)).and ((S.params_consts' A hA).mono fun _ => Dom.mono S.le₁)).mono
        fun x ⟨h1, h2⟩ => h1.symm.trans (hag x h2).symm).mpr hP
  have hown := ownLevels_eval (b := b) hl
  have hSv : ∀ xs : List V, ∀ D, (ps ++ xs).length = D →
      interp (M₃ M b) ls (appN (.const (b.types[0]!).name (ownLevels b.uvars)) (vars D 0 b.nparams))
        (ps ++ xs).reverse = app (carrier M ls b ps.reverse 0) (mkTower []) := by
    intro xs D hD
    rw [interp_appN, interp_vars _ _ hD (by simp [← hD, hplen])]
    simp only [interp, hown, List.drop_zero, List.take_append_of_le_length
        (by omega : b.nparams ≤ ps.length)]
    rw [List.take_of_length_le (by omega)]
    exact S.type_apps h2 h3 hc hps
  have hxS : x ∈ˢ app (carrier M ls b ps.reverse 0) (mkTower []) := by
    have h := hX
    cases h with
    | cons hx _ =>
      have := hSv [] b.nparams (by simp [hplen])
      simp only [List.append_nil] at this hx
      rw [this] at hx; exact hx
  have hi0 : mkTower [] ∈ˢ Is M ls b ps.reverse 0 :=
    mkTower_mem_extSet M _ (by rw [hidx]; exact .nil : Ext M ls (b.types[0]!).indices ps.reverse [])
  obtain ⟨q, c', fs, hq, hfit, -, rfl⟩ := S.mem_carrier_inv hl hps hd0 hi0 hxS
  have hq0 : q = 0 ∧ c' = c := by
    rw [hcs] at hq
    cases q with
    | zero => simp at hq; exact ⟨rfl, hq.symm⟩
    | succ q => simp at hq
  obtain ⟨rfl, rfl⟩ := hq0
  have hfl : fs.length = c'.fields.length := by
    have := FFit.length_eq (M := M) (ls := ls) hfit; simpa using this
  have hW : (ps ++ [enc ls b 0 fs]).length = b.nparams + 1 := by simp [hplen]
  have hvar : interp (M₃ M b) ls (var (b.nparams + 1) b.nparams) (ps ++ [enc ls b 0 fs]).reverse =
      enc ls b 0 fs := by
    rw [interp_var _ _ hW (by omega)]; simp [List.getD_eq_getElem?_getD, hplen]
  refine ⟨?_, by rw [hvar, hSv [enc ls b 0 fs] _ hW]; exact hxS⟩
  rw [hvar, interp_appN, List.map_append, interp_vars _ _ hW (by omega)]
  have hprojs : ((List.range c'.fields.length).map (b.projV c' (b.nparams + 1)
      (var (b.nparams + 1) b.nparams))).map (interp (M₃ M b) ls ·
          (ps ++ [enc ls b 0 fs]).reverse) = fs := by
    apply List.ext_getElem (by simp [hfl])
    intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range]
    rw [S.proj_val h2 h3 hc hl hps hfit (by simpa using hi1)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
  rw [hprojs]
  have e0 : ((ps ++ [enc ls b 0 fs]).drop 0).take b.nparams = ps := by simp [hplen]
  rw [e0]
  simp only [interp, hown, BlockModel.Setting.hctor₃ h2 h3 0 hd0 0 c' hcq]
  have hpsc : Ext (Mc M b) ls b.params [] ps :=
    (Ext.congrM (M := M) (M' := Mc M b) (fun _ h => h) fun A hA =>
      (S.free₀ (S.params_consts' A hA)).mono fun _ h => h.symm).mp hps
  have hc' : c' ∈ (b.types[0]!).ctors := List.mem_of_getElem? hcq
  have hfsc : Ext (Mc M b) ls (c'.fields.map (·.ty)) ps.reverse fs := by
    refine (Ext.congrM (M := M₃ M b) (M' := Mc M b) (fun x hx => hag x hx) fun A hA => ?_).mp
      (S.ffit_ext h2 h3 hc hl hps hfit)
    exact S.fctx_consts hd0 hc' c'.fields.length (Nat.le_refl _) A
      (by simp only [fctx, List.take_length, List.mem_reverse, List.mem_append]; exact .inr hA)
  show enc ls b 0 fs = (ps ++ fs).foldl app (ctorVal b (Mc M b) ls 0 c')
  unfold ctorVal
  rw [List.foldl_append, apps_lamTel hpsc]
  simp only [List.append_nil]
  rw [apps_lamTel hfsc]
  have htk : (fs.reverse ++ ps.reverse).take c'.fields.length = fs.reverse :=
    (List.take_append_of_le_length (by simp [hfl])).trans (List.take_of_length_le (by simp [hfl]))
  rw [htk, List.reverse_reverse]

theorem projV_scoped' {c : SCtor} (hc : b.etaCtor? = some c) (i : Nat) :
    ∀ {d : Nat}, b.nparams ≤ d → i < c.fields.length →
    Scoped (Dom env₃) (d + 1) (b.projV c (d + 1) (var (d + 1) d) i) := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro d hdn hi
  obtain ⟨hnt, -, hcs, -, -, -, hlg⟩ := etaCtor_facts hc
  have hcq : (ctorsOf b 0)[0]? = some c := by rw [hcs]; rfl
  have hd0 : 0 < b.ntypes := by omega
  have hc' : c ∈ (b.types[0]!).ctors := List.mem_of_getElem? hcq
  have hle : ∀ x, Dom env₁ x → Dom env₃ x := fun x hx =>
    Dom.mono (addFold_spec h3).2.2.1 (Dom.mono (addFold_spec h2).2.2.1 hx)
  have hT : Dom env₃ (b.types[0]!).name := hle _ (S.type_dom hd0)
  have hR : Dom env₃ (b.recName 0) :=
    BlockModel.Setting.rec_dom h3 (List.mem_map.mpr ⟨0, List.mem_range.mpr hd0, rfl⟩)
  have hfs : ∀ a < c.fields.length, Scoped (Dom env₃) (b.nparams + a) (c.fields[a]!).ty :=
    fun a ha => S.field_scoped (P := Dom env₃) hle hd0 hc' ha
  have hS : ∀ d, b.nparams ≤ d → Scoped (Dom env₃) d
      (appN (.const (b.types[0]!).name (ownLevels b.uvars)) (vars d 0 b.nparams)) :=
    fun d hd => Scoped.appN (Scoped.const hT) (Scoped.vars (by omega))
  have hEF : ∀ d, b.nparams ≤ d → ∀ j (h : j < (b.etaFields c d).length),
      Scoped (Dom env₃) (d + j) (b.etaFields c d)[j] := by
    intro d hd j hj
    have hj' : j < c.fields.length := by simpa [SBlock.etaFields] using hj
    simp only [SBlock.etaFields, List.getElem_map, List.getElem_range, SBlock.place']
    have := Scoped.place (σ := b.σ1 d) (d := d + j) (hfs j hj')
      (fun L hL => by unfold SBlock.σ1; split <;> omega)
    exact ⟨closedN_consumeAnn _ this.1, constsIn_consumeAnn _ this.2⟩
  have hEFl : ∀ d, (b.etaFields c d).length = c.fields.length := by simp [SBlock.etaFields]
  let nf := c.fields.length
  let ty := (c.fields[i]!).ty
  let g : Nat → VExpr := fun j => if h : j < i then
      have : i - 1 - j < i := by omega
      b.projV c (d + 1 + 1) (var (d + 1 + 1) (d + 1)) (i - 1 - j)
    else var (d + 1 + 1) (b.nparams - 1 - (j - i))
  let F := if !c.fieldDep i then b.place' (b.nparams + i) (d + 1) (d + 1 + 1) ty
    else if b.level.isNeverZero && !c.substField i then
      b.etaFieldTy c (d + 1 + 1) (var (d + 1 + 1) (d + 1)) i
    else subst g ty
  have hproj : b.projV c (d + 1) (var (d + 1) d) i =
      appN (.const (b.recName 0) ((c.fields[i]!).sort :: ownLevels b.uvars))
        (vars (d + 1) 0 b.nparams ++ [.lam (appN (.const (b.types[0]!).name (ownLevels b.uvars))
          (vars (d + 1) 0 b.nparams)) F, Spec.lamTel (b.etaFields c (d + 1))
              (var (d + 1 + nf) (d + 1 + i)),
          var (d + 1) d]) := by
    rw [SBlock.projV]; simp only [hlg, ite_true, Bool.true_and]; rfl
  have hF : Scoped (Dom env₃) (d + 1 + 1) F := by
    by_cases hdep : c.fieldDep i
    · by_cases heta : (b.level.isNeverZero && !c.substField i) = true
      · have e : F = b.etaFieldTy c (d + 1 + 1) (var (d + 1 + 1) (d + 1)) i := by
          simp only [F, hdep, heta]; rfl
        rw [e]
        unfold SBlock.etaFieldTy
        refine Scoped.appN (Scoped.const hR) fun a ha => ?_
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with ha | rfl | rfl | rfl
        · exact Scoped.vars (by omega) a ha
        · exact Scoped.lam (hS _ (by omega)) Scoped.sort
        · refine Scoped.lamTel (hEF _ (by omega)) ?_
          rw [hEFl]
          exact Scoped.place (hfs i hi) (fun L hL => by unfold SBlock.σ1; split <;> omega)
        · exact Scoped.var (by omega)
      ·
        have e : F = subst g ty := by
          simp only [F, hdep, heta]; rfl
        rw [e]
        have hg : ∀ j, j < i → Scoped (Dom env₃) (d + 1 + 1) (g j) := fun j hji => by
          simp only [g, dite_eq_left hji]; exact ih (i - 1 - j) (by omega) (by omega) (by omega)
        have hg' : ∀ j, ¬ j < i → Scoped (Dom env₃) (d + 1 + 1) (g j) := fun j hji => by
          simp only [g, dite_eq_right hji]
          exact Scoped.var (by omega)
        refine ⟨?_, Nested.constsIn_subst (fun j => ?_) (hfs i hi).2⟩
        · have := Nested.closedN_subst (f := g) (N := b.nparams + i) (n := d + 1 + 1)
            (fun j _ => if hji : j < i then (hg j hji).1 else (hg' j hji).1)
            (e := ty) (k := 0) (by rw [Nat.zero_add]; exact (hfs i hi).1)
          simpa using this
        · exact if hji : j < i then (hg j hji).2 else (hg' j hji).2
    · have hnd : c.fieldDep i = false := by simpa using hdep
      have e : F = b.place' (b.nparams + i) (d + 1) (d + 1 + 1) ty := by
        simp only [F, hnd]; rfl
      rw [e]
      exact scoped_place_any (hfs i hi) (by omega)
  rw [hproj]
  refine Scoped.appN (Scoped.const hR) fun a ha => ?_
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with ha | rfl | rfl | rfl
  · exact Scoped.vars (by omega) a ha
  · exact Scoped.lam (hS _ (by omega)) hF
  · refine Scoped.lamTel (hEF _ (by omega)) ?_
    rw [hEFl]
    exact Scoped.var (by omega)
  · exact Scoped.var (by omega)

theorem projV_scoped {c : SCtor} (hc : b.etaCtor? = some c) {i : Nat} (hi : i < c.fields.length) :
    Scoped (Dom env₃) (b.nparams + 1) (b.projV c (b.nparams + 1)
        (var (b.nparams + 1) b.nparams) i) :=
  S.projV_scoped' h2 h3 hc i (Nat.le_refl _) hi

theorem etaTel_scoped {c : SCtor} (hc : b.etaCtor? = some c) :
    ∀ j (h : j < (b.params ++ [appN (.const (b.types[0]!).name (ownLevels b.uvars))
      (vars b.nparams 0 b.nparams)]).length), Scoped (Dom env₃) (0 + j)
      (b.params ++ [appN (.const (b.types[0]!).name (ownLevels b.uvars))
        (vars b.nparams 0 b.nparams)])[j] := by
  obtain ⟨hnt, -, -, -, -, -, -⟩ := etaCtor_facts hc
  have hd0 : 0 < b.ntypes := by omega
  have hle : ∀ x, Dom env₁ x → Dom env₃ x := fun x hx =>
    Dom.mono (addFold_spec h3).2.2.1 (Dom.mono (addFold_spec h2).2.2.1 hx)
  intro j hj
  have hpl : b.params.length = b.nparams := rfl
  by_cases hjn : j < b.nparams
  · rw [List.getElem_append_left (by omega)]
    have := S.params_scoped (P := Dom env₃) hle hjn
    have e : b.params[j]! = b.params[j] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [e] at this; rw [Nat.zero_add]; exact this
  · have hj' : j = b.nparams := by simp at hj; omega
    subst hj'
    rw [List.getElem_append_right (by omega)]
    simp only [hpl, Nat.sub_self, List.getElem_cons_zero, Nat.zero_add]
    exact Scoped.appN (Scoped.const (hle _ (S.type_dom hd0))) (Scoped.vars (by omega))

theorem etaRule_scoped {r : VDefEq} (hr : b.etaRule = some r) :
    Scoped (Dom env₃) 0 r.lhs ∧ Scoped (Dom env₃) 0 r.rhs ∧ Scoped (Dom env₃) 0 r.type := by
  unfold SBlock.etaRule at hr
  cases hc : b.etaCtor? with
  | none => simp [hc] at hr
  | some c =>
    simp only [hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hr
    subst hr
    obtain ⟨hnt, -, hcs, -, -, -, -⟩ := etaCtor_facts hc
    have hcq : (ctorsOf b 0)[0]? = some c := by rw [hcs]; rfl
    have hd0 : 0 < b.ntypes := by omega
    have hle : ∀ x, Dom env₁ x → Dom env₃ x := fun x hx =>
      Dom.mono (addFold_spec h3).2.2.1 (Dom.mono (addFold_spec h2).2.2.1 hx)
    have hD := S.etaTel_scoped h2 h3 hc
    have hDl : (b.params ++ [appN (.const (b.types[0]!).name (ownLevels b.uvars))
        (vars b.nparams 0 b.nparams)]).length = b.nparams + 1 := by simp; rfl
    have hC : Dom env₃ c.name := by
      have := BlockModel.Setting.ctor_dom h2 (mem_ctors_name hcq)
      exact Dom.mono (addFold_spec h3).2.2.1 this
    refine ⟨Scoped.lamTel hD (by rw [hDl, Nat.zero_add]; exact Scoped.var (by omega)),
      Scoped.lamTel hD ?_, Scoped.forallTel hD ?_⟩
    · rw [hDl, Nat.zero_add]
      refine Scoped.appN (Scoped.const hC) fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · exact Scoped.vars (by omega) a ha
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        have := S.projV_scoped h2 h3 hc (List.mem_range.mp hi)
        simpa using this
    · rw [hDl, Nat.zero_add]
      exact Scoped.appN (Scoped.const (hle _ (S.type_dom hd0))) (Scoped.vars (by omega))

theorem eta_law {r : VDefEq} (hr : b.etaRule = some r) {ls : List Nat} (hl : ls.length = r.uvars)
    (ρ : List V) :
    interp (M₃ M b) ls r.lhs ρ = interp (M₃ M b) ls r.rhs ρ ∧
      interp (M₃ M b) ls r.lhs ρ ∈ˢ interp (M₃ M b) ls r.type ρ := by
  obtain ⟨hlS, hrS, htS⟩ := S.etaRule_scoped h2 h3 hr
  rw [interp_closed (M₃ M b) ls hlS.1 ρ, interp_closed (M₃ M b) ls hrS.1 ρ,
    interp_closed (M₃ M b) ls htS.1 ρ]
  unfold SBlock.etaRule at hr
  cases hc : b.etaCtor? with
  | none => simp [hc] at hr
  | some c =>
    simp only [hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hr
    subst hr
    simp only [] at hl ⊢
    rw [interp_lamTel', interp_lamTel', interp_forallTel]
    refine ⟨lamTel_congr fun ws hws => ?_, lamTel_mem_piTel fun ws hws => ?_⟩
    · have := (S.eta_core h2 h3 hc hl hws).1; simpa using this
    · have := (S.eta_core h2 h3 hc hl hws).2; simpa using this

end Setting

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem eta_model {env' : VEnv} (hadd : b.add env = some env') (hM' : IsModel (M₃ M b) env')
    (hG' : Good env') : IsModel (M₃ M b) (b.addEta env') ∧ Good (b.addEta env') := by
  obtain ⟨e₁, e₂, e₃, h1, h2, h3, rfl⟩ := add_spec hadd
  have he : e₁ = env₁ := by rw [S.hwt] at h1; exact (Option.some.inj h1).symm
  subst he
  unfold SBlock.addEta
  split
  · rename_i r hr
    obtain ⟨hlS, hrS, htS⟩ := S.etaRule_scoped h2 h3 hr
    have hP : ∀ {e : VExpr}, Scoped (Dom e₃) 0 e → Scoped (Dom (iotaFold b e₃)) 0 e :=
      fun h => ⟨h.1, h.2.mono fun _ hx => dom_iotaFold.mpr hx⟩
    exact ⟨IsModel.addDefEq hM' fun ls hl ρ => S.eta_law h2 h3 hr hl ρ,
      Good.addDefEq hG' (hP hlS) (hP hrS) (hP htS)⟩
  · exact ⟨hM', hG'⟩

end Setting

end BlockModel
end Soulgem
