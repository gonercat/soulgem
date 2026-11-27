import Soulgem.Model.BlockFinal

/-! # The iota laws -/

namespace Soulgem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V]

theorem lamTel_transfer {M₁ M₂ : CInterp V} {ls₁ ls₂ : List Nat} {B₁ B₂ : List V → V} :
    ∀ {As Bs : List VExpr} {ρ₁ ρ₂ : List V}, As.length = Bs.length →
    (∀ i (h : i < As.length) (h' : i < Bs.length) (ys : List V), Ext M₂ ls₂ (Bs.take i) ρ₂ ys →
      interp M₁ ls₁ As[i] (ys.reverse ++ ρ₁) = interp M₂ ls₂ Bs[i] (ys.reverse ++ ρ₂)) →
    (∀ ys, Ext M₂ ls₂ Bs ρ₂ ys → B₁ (ys.reverse ++ ρ₁) = B₂ (ys.reverse ++ ρ₂)) →
    Soulgem.lamTel M₁ ls₁ As B₁ ρ₁ = Soulgem.lamTel M₂ ls₂ Bs B₂ ρ₂
  | [], [], _, _, _, _, hB => by simpa [Soulgem.lamTel] using hB [] .nil
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | A :: As, B :: Bs, ρ₁, ρ₂, hl, h, hB => by
    simp only [Soulgem.lamTel]
    have h0 := h 0 (by simp) (by simp) [] .nil
    simp only [List.reverse_nil, List.nil_append, List.getElem_cons_zero] at h0
    rw [h0]
    refine clam_congr fun x hx => lamTel_transfer (by simpa using hl) (fun i hi hi' ys hys => ?_)
      fun ys hys => ?_
    · have := h (i + 1) (by simp; omega) (by simp; omega) (x :: ys) (by simpa using Ext.cons hx hys)
      simpa using this
    · have := hB (x :: ys) (.cons hx hys)
      simpa using this

theorem mkTower_inj_of_length {xs ys : List V} (h : mkTower xs = mkTower ys)
    (hl : xs.length = ys.length) : xs = ys := by
  have h1 := projList_mkTower xs.length xs rfl
  have h2 := projList_mkTower xs.length ys hl.symm
  rw [h] at h1
  exact h1.symm.trans h2

theorem recLevels_eval (b : SBlock) {ls : List Nat} (hl : ls.length = b.recUvars) :
    b.recLevels.map (VLevel.eval ls) = ls := by
  apply List.ext_getElem (by simp [SBlock.recLevels, hl])
  intro i h1 h2
  simp only [SBlock.recLevels, List.getElem_map, List.getElem_range, VLevel.eval]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

namespace BlockModel
open BlockSem Setting

variable (M : CInterp V) (b : SBlock) in
theorem rec_apply {M'' : CInterp V} {ls' : List Nat} {k : Nat} {ps mots mins iv : List V} {x : V}
    (hplen : ps.length = b.nparams) (hmotl : mots.length = b.ntypes)
        (hminl : mins.length = b.nctors)
    (hivl : iv.length = (b.types[k]!).indices.length)
    (hext : Ext M'' ls' (b.preTel ++ recIdx b k ++ [recMajor b k]) []
        (ps ++ mots ++ mins ++ iv ++ [x])) :
    (ps ++ mots ++ mins ++ iv ++ [x]).foldl app (recVal M b M'' k ls') =
      recAt M (blev b ls') b ps.reverse (elimLev b ls') mots mins (tagged k (mkTower iv) x) := by
  have hpre : b.pre = b.nparams + b.ntypes + b.nctors := rfl
  unfold recVal
  rw [apps_lamTel hext]
  simp only [List.append_nil, List.reverse_reverse]
  unfold recRes
  have e_ps : (ps ++ mots ++ mins ++ iv ++ [x]).take b.nparams = ps := by
    simp [List.append_assoc, hplen]
  have e_mots : ((ps ++ mots ++ mins ++ iv ++ [x]).drop b.nparams).take b.ntypes = mots := by
    simp [List.append_assoc, hplen, hmotl]
  have e_mins : ((ps ++ mots ++ mins ++ iv ++ [x]).drop (b.nparams + b.ntypes)).take b.nctors
      = mins := by
    rw [show b.nparams + b.ntypes = (ps ++ mots).length by simp [hplen, hmotl]]
    simp [List.append_assoc, hminl]
  have e_is : ((ps ++ mots ++ mins ++ iv ++ [x]).drop b.pre).take
      (b.types[k]!).indices.length = iv := by
    rw [show b.pre = (ps ++ mots ++ mins).length by simp only [List.length_append]; omega]
    simp [List.append_assoc, hivl]
  have e_x : (ps ++ mots ++ mins ++ iv ++ [x]).getD (b.pre + (b.types[k]!).indices.length)
      pt = x := by
    rw [show b.pre + (b.types[k]!).indices.length = (ps ++ mots ++ mins ++ iv).length by
      simp only [List.length_append]; omega]
    simp
  rw [e_ps, e_mots, e_mins, e_is, e_x]

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem ctor_result {ls : List Nat} (hl : ls.length = b.uvars) {j q : Nat} {c : SCtor}
    (hcq : (ctorsOf b j)[q]? = some c) {ps : List V} (hps : Ext M ls b.params [] ps) {fs : List V}
    (hfit : FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fs) :
    Ext M ls (b.types[j]!).indices ps.reverse (c.idx.map (interp M ls ·
        (fs.reverse ++ ps.reverse))) := by
  have hj := lt_of_ctor hcq
  have hc : c ∈ (b.types[j]!).ctors := List.mem_of_getElem? hcq
  have hC := carrier_tupleFn M b
  have hM₁ := (S.model₁ hC).1
  have hidxl := (S.ctorSyn hj hc).idx_len
  have hidxm := (S.ctorSyn hj hc).idx_free
  have hidxty := (S.ctorOK j hj c hc).idx_typed
  have hctx := S.fctx_consts hj hc c.fields.length (Nat.le_refl _)
  have hfctx : fctx b c c.fields.length = (b.params ++ c.fields.map (·.ty)).reverse :=
      by simp [fctx]
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M ls hps]; rfl
  have hflen : fs.length = c.fields.length := hfit.length_eq
  have hsat : Sat (M₁ M b fun ls ρp => carrier M ls b ρp) ls (fctx b c c.fields.length)
      (fs.reverse ++ ps.reverse) :=
    (S.ffit_iff_sat hC hl hj hc hps c.fields.length (Nat.le_refl _) fs hflen).mp
        (by simpa using hfit)
  have hrev : fs.reverse ++ ps.reverse = (ps ++ fs).reverse := by simp
  have htake : (ps ++ fs).take b.nparams = ps := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hfit' := BlockModel.idx_fit_gen (M := M) hM₁ (Γ := (b.params ++ c.fields.map (·.ty)).reverse)
    (zs := ps ++ fs) (by rw [← hrev, ← hfctx]; exact hsat)
    (n := b.nparams) (E := c.fields.length) (by simp [hplen, hflen]) hidxl
    (fun l hl' => by
      have := hidxty l hl'
      rw [idxType_eq] at this
      exact this)
    (fun l hl' => S.indices_closed hj hl') (fun A hA => S.free₀ (S.indices_consts hj A hA))
  rw [htake] at hfit'
  have hci : ∀ i ∈ c.idx, ConstsIn (Dom env₁) i := fun i hi => by
    obtain ⟨l, hl', rfl⟩ := List.mem_iff_getElem.mp hi
    have := hidxty l hl'
    have e : c.idx[l]! = c.idx[l] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl']; rfl
    rw [e] at this
    exact (IsDefEq.constsIn S.good₁.2 this (by rw [← hfctx]; exact hctx)).1
  have e : c.idx.map (interp (M₁ M b fun ls ρp => carrier M ls b ρp) ls · (ps ++ fs).reverse) =
      c.idx.map (interp M ls · (fs.reverse ++ ps.reverse)) := by
    rw [← hrev]; exact List.map_congr_left fun i hi => interp_congr
        (S.free (hci i hi) (hidxm i hi)) _
  rwa [e] at hfit'

theorem ext_fields_sh {M' : CInterp V} {ls' : List Nat} {ps : List V}
    (hplen : ps.length = b.nparams) {j : Nat} (hj : j < b.ntypes) {c : SCtor}
    (hc : c ∈ (b.types[j]!).ctors) {mid : List V} {D : Nat} (hD : ps.length + mid.length = D)
    (zs : List V) :
    Ext M' ls' ((List.range c.fields.length).map fun a =>
        b.sh (place (b.nparams + a) (b.σ1 D) (D + a) (c.fields[a]!).ty)) (ps ++ mid).reverse zs ↔
      Ext M' (blev b ls') (c.fields.map (·.ty)) ps.reverse zs := by
  refine ext_transfer (by simp) fun a ha ha' ys hys => ?_
  have ha2 : a < c.fields.length := by simpa using ha'
  have hya : ys.length = a := by
    rw [Ext.length_eq _ _ hys, List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt ha')
  have hrev : ys.reverse ++ (ps ++ mid).reverse = (ps ++ mid ++ ys).reverse := by simp
  rw [hrev]
  simp only [List.getElem_map, List.getElem_range]
  have hsc := S.field_scoped (P := fun _ => True) (fun _ _ => trivial) hj hc ha2
  rw [interp_sh_place M' ls' b (b.nparams + a) (b.σ1 D) (D + a) _ (ps ++ mid ++ ys) hsc.1
    (by simp only [List.length_append]; omega) (fun L hL => by unfold SBlock.σ1; split <;> omega),
    pull_σ1 b hplen hD a hya, List.reverse_append]
  have e : c.fields[a]! = c.fields[a] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha2]; rfl
  rw [e]

theorem pre_facts {M' : CInterp V} (hag : ∀ x, Dom env₁ x → M' x = Mc M b x)
    (hM' : IsModel M' env₁)
    (hctor : ∀ j < b.ntypes, ∀ (q : Nat) (c : SCtor), (ctorsOf b j)[q]? = some c →
      M' c.name = fun ls => ctorVal b (Mc M b) ls q c)
    {ls' : List Nat} {ps mots mins : List V}
    (hP : Ext M' ls' ((List.range b.nparams).map fun i => b.binder b.params[i]!) [] ps)
    (hT : Ext M' ls' ((List.range b.ntypes).map b.motiveTy) (ps.reverse ++ []) mots)
    (hN : Ext M' ls' (minorList b) ((ps ++ mots).reverse ++ []) mins) :
    Ext M (blev b ls') b.params [] ps ∧ mots.length = b.ntypes ∧ mins.length = b.nctors ∧
      HMot M (blev b ls') b ps.reverse (elimLev b ls') mots ∧
      HMin M (blev b ls') b ps.reverse mots mins := by
  have hmotl : mots.length = b.ntypes := by rw [Ext.length_eq _ _ hT]; simp
  have hminl : mins.length = b.nctors := by rw [Ext.length_eq _ _ hN, minorList_length]
  have hps : Ext M (blev b ls') b.params [] ps := (S.ext_params hag hM' ps).mp hP
  have hmots : ∀ j < b.ntypes, mots.getD j pt ∈ˢ motSp M b (blev b ls') ps (elimLev b ls') j := by
    intro j hj
    have hj' : j < mots.length := by omega
    have := hT.get j (by simpa using hj) hj'
    simp only [List.getElem_map, List.getElem_range, List.append_nil] at this
    rw [S.interp_motiveTy' hag hps hj (by simp; omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    exact this
  have hmins : ∀ j < b.ntypes, ∀ q c, (ctorsOf b j)[q]? = some c →
      mins.getD (b.ctorBase j + q) pt ∈ˢ interp M' ls'
        (b.minorTy j c (b.nparams + b.ntypes + b.ctorBase j + q))
        (ps ++ mots ++ mins.take (b.ctorBase j + q)).reverse := by
    intro j _ q c hcq
    have hg := minorList_getElem? b hcq
    have hlt0 : b.ctorBase j + q < b.nctors := ctorBase_add_lt hcq
    have hlt : b.ctorBase j + q < (minorList b).length := by rw [minorList_length]; exact hlt0
    have hlt' : b.ctorBase j + q < mins.length := by omega
    have := hN.get (b.ctorBase j + q) hlt hlt'
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hg
    rw [hg] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt']
    simpa using this
  exact ⟨hps, hmotl, hminl, BlockModel.Setting.hMot hps hmots,
      S.hMin hag hM' hctor hps hmotl (by omega) hmins⟩

end Setting
namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S
variable {env₂ env₃ : VEnv} (h2 : addFold env₁ (ctorConsts b) = some env₂)
  (h3 : addFold env₂ (recConsts b) = some env₃)
include h2 h3

omit S in
theorem hag₃₁ : ∀ x, Dom env₁ x → M₃ M b x = Mc M b x := fun x hx =>
  (BlockModel.Setting.hag₃ h3 x (Dom.mono (addFold_spec h2).2.2.1 hx)).trans
      (BlockModel.Setting.hag₂ h2 x hx)

theorem model₃₁ : IsModel (M₃ M b) env₁ :=
  IsModel.congr (S.model₁ (carrier_tupleFn M b)).1 S.good₁ (BlockModel.Setting.hag₃₁ h2 h3)

omit S in
theorem hctor₃ : ∀ j < b.ntypes, ∀ (q : Nat) (c : SCtor), (ctorsOf b j)[q]? = some c →
    M₃ M b c.name = fun ls => ctorVal b (Mc M b) ls q c := fun j hj q c hcq =>
  (BlockModel.Setting.hag₃ h3 _ (BlockModel.Setting.ctor_dom h2 (mem_ctors_name hcq))).trans
      (BlockModel.Setting.hctor₂ h2 j hj q c hcq)

theorem rec_call_eq {ls : List Nat} (hl : ls.length = b.recUvars) {ps mots mins : List V}
    (hpre : Ext (M₃ M b) ls b.preTel [] (ps ++ mots ++ mins)) (hps :
        Ext M (blev b ls) b.params [] ps)
    (hmotl : mots.length = b.ntypes) (hminl : mins.length = b.nctors) {k : Nat} (hk : k < b.ntypes)
    {iv : List V} {x : V} (hiv : Ext M (blev b ls) (b.types[k]!).indices ps.reverse iv)
    (hx : x ∈ˢ app (carrier M (blev b ls) b ps.reverse k) (mkTower iv)) :
    (ps ++ mots ++ mins ++ iv ++ [x]).foldl app
        (M₃ M b (b.recName k) (b.recLevels.map (VLevel.eval ls))) =
      recAt M (blev b ls) b ps.reverse (elimLev b ls) mots mins (tagged k (mkTower iv) x) := by
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hivl : iv.length = (b.types[k]!).indices.length := Ext.length_eq M _ hiv
  have hD : ps.length + (mots ++ mins).length = b.pre := by
    simp only [List.length_append]; show _ = b.nparams + b.ntypes + b.nctors; omega
  rw [recLevels_eval b hl, M₃_rec (BlockModel.Setting.rec_nodup h3) hk]
  simp only []
  refine rec_apply M b hplen hmotl hminl hivl ?_
  have hidx : Ext (M₃ M b) ls (recIdx b k) ((ps ++ mots ++ mins).reverse ++ []) iv := by
    have e : (ps ++ mots ++ mins).reverse ++ [] = (ps ++ (mots ++ mins)).reverse := by simp
    rw [e]
    exact (S.ext_indices (BlockModel.Setting.hag₃₁ h2 h3) (S.model₃₁ h2 h3) hps hk hD iv).mpr hiv
  have hmaj : Ext (M₃ M b) ls [recMajor b k] ((ps ++ mots ++ mins ++ iv).reverse ++ []) [x] := by
    refine .cons ?_ .nil
    have e : (ps ++ mots ++ mins ++ iv).reverse ++ [] = (ps ++ (mots ++ mins) ++ iv).reverse := by
      simp
    rw [e, S.interp_major (BlockModel.Setting.hag₃₁ h2 h3) hps hk hD hiv]
    exact hx
  have h₃ := Ext.append (Ext.append hpre hidx) hmaj
  have hcons : ∀ A ∈ b.preTel ++ recIdx b k ++ [recMajor b k], ConstsIn (Dom env₂) A := by
    have := (S.rec_type_scoped h2 (fun _ h => h) hk).2
    rw [recType_eq, constsIn_forallTel] at this
    exact this.1
  exact (Ext.congrM (fun x hx => BlockModel.Setting.hag₃ h3 x hx) hcons).mp h₃

theorem ih_binder {ls : List Nat} {ps mid fsv ys : List V} (hps : Ext M (blev b ls) b.params [] ps)
    {j q : Nat} {c : SCtor} (hcq : (ctorsOf b j)[q]? = some c)
    (hfE : Ext (M₃ M b) (blev b ls) (c.fields.map (·.ty)) ps.reverse fsv)
    {D E : Nat} (hD : ps.length + mid.length = D) (hE : D + fsv.length + ys.length = E)
    {a : Nat} {xs : List VExpr} {k : Nat} {idx : List VExpr} (hR : (a, xs, k, idx) ∈ c.recFields)
    {e : Nat} (he : e < xs.length) {zs : List V} (hzs : Ext M (blev b ls) (xs.take e)
        (pre ps.reverse fsv a) zs) :
    interp (M₃ M b) ls (b.binder (place (b.nparams + a + e) (b.σ2 a D E) (E + e) xs[e]!))
        (zs.reverse ++ (ps ++ mid ++ fsv ++ ys).reverse) =
      interp M (blev b ls) xs[e] (zs.reverse ++ pre ps.reverse fsv a) := by
  have hj := lt_of_ctor hcq
  have hc : c ∈ (b.types[j]!).ctors := List.mem_of_getElem? hcq
  obtain ⟨ha, hcert⟩ := recFields_mem hR
  simp only at ha hcert
  obtain ⟨_, _, hxs, _, hann, hcl, _⟩ := S.rec_field hj hc ha hcert
  have hag := BlockModel.Setting.hag₃₁ (M := M) h2 h3
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hfl : fsv.length = c.fields.length := by rw [Ext.length_eq _ _ hfE]; simp
  have hpsM : Ext (M₃ M b) (blev b ls) b.params [] ps :=
    (Ext.congrM (fun x h => h) fun A hA => ((S.free₀ (C := fun ls ρp => carrier M ls b ρp)
      (S.params_consts' A hA)).and ((S.params_consts' A hA).mono fun _ => Dom.mono S.le₁)).mono
        fun x ⟨h1, h2⟩ => h1.symm.trans (hag x h2).symm).mp hps
  have hpS : Sat (M₃ M b) (blev b ls) b.params.reverse ps.reverse := by
    simpa using Sat.of_ext (Γ := []) (ρ := []) trivial hpsM
  have hsatA : Sat (M₃ M b) (blev b ls) (fctx b c a) (ps ++ fsv.take a).reverse := by
    have h1 := (Ext.split (As := (c.fields.map (·.ty)).take a) (Bs := (c.fields.map (·.ty)).drop a)
      (by rw [List.take_append_drop]; exact hfE)).1
    have h2 := Sat.of_ext hpS h1
    simpa [fctx, List.map_take, Nat.min_eq_left (Nat.le_of_lt ha)] using h2
  have hag' : ∀ x ∈ xs, ConstsIn (fun y => M y = M₃ M b y) x := fun x hx =>
    (S.free' hag (hxs x hx).1 (hxs x hx).2).mono fun _ h => h.symm
  have hze : zs.length = e := by
    rw [Ext.length_eq _ _ hzs, List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt he)
  have hrev : zs.reverse ++ (ps ++ mid ++ fsv ++ ys).reverse =
      (ps ++ mid ++ fsv ++ ys ++ zs).reverse := by
    simp
  rw [hrev]
  have hpull := pull_σ2 b (mid := mid) (fs := fsv) (mid2 := ys) (zs := zs) hplen hD hE
    (Nat.le_of_lt (hfl ▸ ha))
  rw [hze] at hpull
  have hzs' : Ext (M₃ M b) (blev b ls) (xs.take e) (ps ++ fsv.take a).reverse zs := by
    have := (Ext.congrM (fun _ h => h) fun A hA => hag' A (List.mem_of_mem_take hA)).mp hzs
    simpa [pre] using this
  rw [interp_binder_place (S.model₃₁ h2 h3) S.good₁.1 ls b (hcl e (Nat.le_of_lt he))
      (b.nparams + a + e)
    (by simp only [fctx, List.length_append, List.length_reverse, List.length_map,
        List.length_take, Nat.min_eq_left (Nat.le_of_lt ha), Nat.min_eq_left (Nat.le_of_lt he)]
        show e + (b.nparams + a) = b.nparams + a + e; omega)
    (b.σ2 a D E) (E + e) _ (hann e he) (ps ++ mid ++ fsv ++ ys ++ zs)
    (by simp only [List.length_append]; omega)
    (fun L hL => by unfold SBlock.σ2; split; omega; split <;> omega)
    (by rw [hpull]; have := Sat.of_ext hsatA hzs'; simpa using this)]
  rw [hpull]
  have e' : xs[e]! = xs[e] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem he]; rfl
  rw [e', interp_congr (S.free' hag (hxs _ (List.getElem_mem he)).1
      (hxs _ (List.getElem_mem he)).2)]
  simp [pre]

end Setting

abbrev iotaΔ (b : SBlock) (d q : Nat) : List VExpr := b.preTel ++ (b.rulePieces d q).1
abbrev iotaL (b : SBlock) (d q : Nat) : VExpr :=
  .app (appN (.const (b.recName d) b.recLevels)
    (vars (b.pre + (b.rulePieces d q).1.length) 0 b.pre ++ (b.rulePieces d q).2.2.1))
    (b.rulePieces d q).2.2.2.1
abbrev iotaR (b : SBlock) (d q : Nat) : VExpr := (b.rulePieces d q).2.2.2.2
abbrev iotaT (b : SBlock) (d q : Nat) : VExpr :=
  .app (appN (var (b.pre + (b.rulePieces d q).1.length) (b.nparams + d)) (b.rulePieces d q).2.2.1)
    (b.rulePieces d q).2.2.2.1

theorem iota_eq (b : SBlock) (d q : Nat) : b.iota d q =
    { uvars := b.recUvars, lhs := Spec.lamTel (iotaΔ b d q) (iotaL b d q),
      rhs := Spec.lamTel (iotaΔ b d q) (iotaR b d q),
      type := Spec.forallTel (iotaΔ b d q) (iotaT b d q) } := rfl

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S
variable {env₂ env₃ : VEnv} (h2 : addFold env₁ (ctorConsts b) = some env₂)
  (h3 : addFold env₂ (recConsts b) = some env₃)
include h2 h3

theorem iota_core {d q : Nat} {c : SCtor} (hcq : (ctorsOf b d)[q]? = some c) {ls : List Nat}
    (hl : ls.length = b.recUvars) {ws : List V} (hws : Ext (M₃ M b) ls (iotaΔ b d q) [] ws) :
    interp (M₃ M b) ls (iotaL b d q) (ws.reverse ++ []) = interp (M₃ M b) ls (iotaR b d q)
        (ws.reverse ++ []) ∧
      interp (M₃ M b) ls (iotaL b d q) (ws.reverse ++ []) ∈ˢ
        interp (M₃ M b) ls (iotaT b d q) (ws.reverse ++ []) := by
  have hd := lt_of_ctor hcq
  have hc : c ∈ (b.types[d]!).ctors := List.mem_of_getElem? hcq
  have hc' : (b.types[d]!).ctors[q]! = c := by
    rw [List.getElem!_eq_getElem?_getD, show (b.types[d]!).ctors = ctorsOf b d from rfl, hcq]; rfl
  have hag := BlockModel.Setting.hag₃₁ (M := M) h2 h3
  have hM3 := S.model₃₁ h2 h3
  have hpre : b.pre = b.nparams + b.ntypes + b.nctors := rfl
  have hlb := blev_length b ls
  obtain ⟨hidxl, hidx⟩ := S.ctor_idx hd hc
  unfold iotaΔ at hws
  unfold iotaL iotaR iotaT
  unfold SBlock.rulePieces at hws ⊢
  simp only [hc', List.length_map, List.length_range, List.append_nil] at hws ⊢
  rw [preTel_eq] at hws
  obtain ⟨w3, fsv, rfl, h3', hF⟩ := Ext.append_inv hws
  obtain ⟨w2, mins, rfl, h2', hN⟩ := Ext.append_inv h3'
  obtain ⟨ps, mots, rfl, hP, hT⟩ := Ext.append_inv h2'
  obtain ⟨hps, hmotl, hminl, hmot, hmin⟩ := S.pre_facts hag hM3
      (BlockModel.Setting.hctor₃ h2 h3) hP hT hN
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hD : ps.length + (mots ++ mins).length = b.pre := by simp only [List.length_append]; omega
  have hpre3 : Ext (M₃ M b) ls b.preTel [] (ps ++ mots ++ mins) := by rw [preTel_eq]; exact h3'
  have hF' : Ext (M₃ M b) ls ((List.range c.fields.length).map fun a =>
      b.sh (place (b.nparams + a) (b.σ1 b.pre) (b.pre + a) (c.fields[a]!).ty))
      (ps ++ (mots ++ mins)).reverse fsv := by
    have e : (ps ++ (mots ++ mins)).reverse = (ps ++ mots ++ mins).reverse ++ [] := by simp
    rw [e]; exact hF
  have hfE := (S.ext_fields_sh hplen hd hc hD fsv).mp hF'
  have hfl : fsv.length = c.fields.length := by rw [Ext.length_eq _ _ hfE]; simp
  have hpsM : Ext (M₃ M b) (blev b ls) b.params [] ps :=
    (Ext.congrM (fun x h => h) fun A hA => ((S.free₀ (C := fun ls ρp => carrier M ls b ρp)
      (S.params_consts' A hA)).and ((S.params_consts' A hA).mono fun _ => Dom.mono S.le₁)).mono
        fun x ⟨h1, h2⟩ => h1.symm.trans (hag x h2).symm).mp hps
  have hpS : Sat (M₃ M b) (blev b ls) b.params.reverse ps.reverse := by
    simpa using Sat.of_ext (Γ := []) (ρ := []) trivial hpsM
  have hsat3 : Sat (M₃ M b) (blev b ls) (fctx b c c.fields.length) (fsv.reverse ++ ps.reverse) := by
    have := Sat.of_ext hpS hfE; simpa [fctx] using this
  have hsatc := (Sat.congrM' (M' := Mc M b) (fun x hx => hag x hx)
    (S.fctx_consts hd hc c.fields.length (Nat.le_refl _))).mp hsat3
  have hfit : FFit M (blev b ls) (carrier M (blev b ls) b ps.reverse) c.fields ps.reverse fsv := by
    have := (S.ffit_iff_sat (carrier_tupleFn M b) hlb hd hc hps c.fields.length (Nat.le_refl _) fsv
      hfl).mpr hsatc
    simpa using this
  let iv := c.idx.map (interp M (blev b ls) · (fsv.reverse ++ ps.reverse))
  have hiv : Ext M (blev b ls) (b.types[d]!).indices ps.reverse iv := S.ctor_result hlb hcq hps hfit
  have hK := S.hK
  have hs := S.hSmall hlb hps
  have hB := S.hBound hlb hps
  have hi : mkTower iv ∈ˢ Is M (blev b ls) b ps.reverse d := mkTower_mem_extSet M _ hiv
  have henc := enc_mem hK hs hB hd hcq hfit hi
  have hu : tagged d (mkTower iv) (enc (blev b ls) b q fsv) ∈ˢ U M (blev b ls) b ps.reverse :=
    mem_unionSet.mpr ⟨d, hd, _, hi, _, henc, rfl⟩
  have hdec : Dec M (blev b ls) b ps.reverse (tagged d (mkTower iv) (enc (blev b ls) b q fsv))
      (d, q, fsv) :=
    ⟨mkTower iv, hi, ⟨c, hcq, hfit, rfl⟩, rfl⟩
  have huq : elimLev b ls ≠ 0 → lev (blev b ls) b = 0 → HUniq M (blev b ls) b ps.reverse := by
    intro hr h0
    have hlarge : b.large = true := by
      unfold elimLev at hr; split at hr
      · assumption
      · exact absurd rfl hr
    exact S.hUniq hlb hps h0 hlarge
  have hW : (ps ++ mots ++ mins ++ fsv).length = b.pre + c.fields.length := by
    simp only [List.length_append]; omega
  have hWa : ps ++ mots ++ mins ++ fsv = ps ++ (mots ++ mins) ++ fsv := by simp
  have hidxv : (c.idx.map fun t => b.sh (place (b.nparams + c.fields.length) (b.σ1 b.pre)
      (b.pre + c.fields.length) t)).map (interp (M₃ M b) ls · (ps ++ mots ++ mins ++
          fsv).reverse) = iv := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    obtain ⟨htc, htd, htm⟩ := hidx t ht
    simp only [Function.comp]
    rw [interp_sh_place (M₃ M b) ls b _ _ _ t _ htc hW (fun L hL =>
        by unfold SBlock.σ1; split <;> omega),
      hWa, pull_σ1 b hplen hD c.fields.length hfl, interp_congr (S.free' hag htd htm),
          List.reverse_append]
  have hpsc : Ext (Mc M b) (blev b ls) b.params [] ps :=
    (Ext.congrM (M := M) (M' := Mc M b) (fun _ h => h) fun A hA =>
      (S.free₀ (S.params_consts' A hA)).mono fun _ h => h.symm).mp hps
  have hfsc : Ext (Mc M b) (blev b ls) (c.fields.map (·.ty)) ps.reverse fsv := by
    refine (Ext.congrM (M := M₃ M b) (M' := Mc M b) (fun x hx => hag x hx) fun A hA => ?_).mp hfE
    exact S.fctx_consts hd hc c.fields.length (Nat.le_refl _) A
      (by simp only [fctx, List.take_length, List.mem_reverse, List.mem_append]; exact .inr hA)
  have hintro : interp (M₃ M b) ls (appN (.const c.name b.blockLevels)
      (vars (b.pre + c.fields.length) 0 b.nparams ++ vars (b.pre + c.fields.length) b.pre
          c.fields.length))
      (ps ++ mots ++ mins ++ fsv).reverse = enc (blev b ls) b q fsv := by
    rw [interp_appN, List.map_append, interp_vars _ _ hW (by omega), interp_vars _ _ hW (by omega)]
    have e0 : ((ps ++ mots ++ mins ++ fsv).drop 0).take b.nparams = ps := by simp [hplen]
    have eD : ((ps ++ mots ++ mins ++ fsv).drop b.pre).take c.fields.length = fsv := by
      rw [show b.pre = (ps ++ mots ++ mins).length by simp only [List.length_append]; omega,
        List.drop_left, ← hfl, List.take_length]
    rw [e0, eD]
    simp only [interp, BlockModel.Setting.hctor₃ h2 h3 d hd q c hcq]
    show (ps ++ fsv).foldl app (ctorVal b (Mc M b) (blev b ls) q c) = _
    unfold ctorVal
    rw [List.foldl_append, apps_lamTel hpsc]
    simp only [List.append_nil]
    rw [apps_lamTel hfsc]
    have htk : (fsv.reverse ++ ps.reverse).take c.fields.length = fsv.reverse :=
      (List.take_append_of_le_length (by simp [hfl])).trans (List.take_of_length_le (by simp [hfl]))
    rw [htk, List.reverse_reverse]
  have hL : interp (M₃ M b) ls (.app (appN (.const (b.recName d) b.recLevels)
      (vars (b.pre + c.fields.length) 0 b.pre ++ c.idx.map fun t =>
          b.sh (place (b.nparams + c.fields.length)
        (b.σ1 b.pre) (b.pre + c.fields.length) t)))
      (appN (.const c.name b.blockLevels)
        (vars (b.pre + c.fields.length) 0 b.nparams ++ vars (b.pre + c.fields.length) b.pre
            c.fields.length)))
      (ps ++ mots ++ mins ++ fsv).reverse =
      recAt M (blev b ls) b ps.reverse (elimLev b ls) mots mins
        (tagged d (mkTower iv) (enc (blev b ls) b q fsv)) := by
    simp only [interp]
    rw [hintro, interp_appN, List.map_append, interp_vars _ _ hW (by omega), hidxv]
    have e0 : ((ps ++ mots ++ mins ++ fsv).drop 0).take b.pre = ps ++ mots ++ mins := by
      simp only [List.drop_zero]
      rw [show b.pre = (ps ++ mots ++ mins).length by simp only [List.length_append]; omega,
        List.take_left]
    have hfold : ∀ (l : List V) (x y : V), app (l.foldl app x) y = (l ++ [y]).foldl app x :=
      fun l x y => by rw [List.foldl_append]; rfl
    rw [e0, hfold]
    exact S.rec_call_eq h2 h3 hl hpre3 hps hmotl hminl hd hiv henc
  rw [hL]
  have hstep := rec_eq hK hs hB hmot hmin huq hu hdec
  refine ⟨?_, ?_⟩
  · rw [interp_appN, List.map_append, interp_vars _ _ hW (by omega), List.map_map]
    have eD : ((ps ++ mots ++ mins ++ fsv).drop b.pre).take c.fields.length = fsv := by
      rw [show b.pre = (ps ++ mots ++ mins).length by simp only [List.length_append]; omega,
        List.drop_left, ← hfl, List.take_length]
    have hmin' : interp (M₃ M b) ls (var (b.pre + c.fields.length)
        (b.nparams + b.ntypes + b.ctorBase d + q))
        (ps ++ mots ++ mins ++ fsv).reverse = mins.getD (b.ctorBase d + q) pt := by
      have hlt := ctorBase_add_lt hcq
      rw [interp_var _ _ hW (by omega)]
      rw [show ps ++ mots ++ mins ++ fsv = (ps ++ mots) ++ (mins ++ fsv) by simp,
        getD_append_right' (by simp only [List.length_append]; omega),
        show b.nparams + b.ntypes + b.ctorBase d + q - (ps ++ mots).length = b.ctorBase d + q by
          simp only [List.length_append]; omega,
        getD_append_left' (by omega)]
    rw [eD, hmin', List.map_congr_left (g := ihVal M (blev b ls) ps.reverse
      (graph (recAt M (blev b ls) b ps.reverse (elimLev b ls) mots mins)
        (pred M (blev b ls) b ps.reverse (d, q, fsv))) fsv) ?ih, hstep]
    · unfold st
      simp only [hcq]
    case ih =>
      intro x hx
      obtain ⟨a, xs, k, idx⟩ := x
      obtain ⟨ha, hcert⟩ := recFields_mem hx
      simp only at ha hcert
      obtain ⟨hk, hidxlR, hxs, hidxR, _, _, hidxc⟩ := S.rec_field hd hc ha hcert
      have hcert' : (c.fields[a]).cert = .recursive xs k idx := by
        rw [← hcert, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha]; rfl
      simp only [Function.comp]
      rw [interp_lamTel']
      unfold ihVal
      simp only []
      refine lamTel_transfer (M₂ := M) (ls₂ := blev b ls) (Bs := xs) (by simp)
        (fun e he he' zs hzs => ?_) fun zs hzs => ?_
      · simp only [List.getElem_map, List.getElem_range]
        have e0 : (ps ++ mots ++ mins ++ fsv).reverse = (ps ++ (mots ++ mins) ++ fsv ++
            []).reverse := by simp
        rw [e0]
        exact S.ih_binder h2 h3 hps hcq hfE (mid := mots ++ mins) (ys := []) hD
          (by simp only [List.length_nil, Nat.add_zero, hfl]) hx he' hzs
      · have hzl : zs.length = xs.length := Ext.length_eq _ _ hzs
        have htk : ((zs.reverse ++ pre ps.reverse fsv a).take xs.length).reverse = zs := by
          rw [List.take_append_of_le_length (by simp [hzl]), List.take_of_length_le (by simp [hzl]),
            List.reverse_reverse]
        simp only [htk]
        have hrev : zs.reverse ++ (ps ++ mots ++ mins ++ fsv).reverse =
            (ps ++ mots ++ mins ++ fsv ++ zs).reverse := by simp
        rw [hrev]
        have hW2 : (ps ++ mots ++ mins ++ fsv ++ zs).length = b.pre + c.fields.length +
            xs.length := by
          simp only [List.length_append]; omega
        have hpullR := pull_σ2 b (mid := mots ++ mins) (fs := fsv) (mid2 := []) (zs := zs) hplen hD
          (E := b.pre + c.fields.length) (by simp only [List.length_nil, Nat.add_zero, hfl])
          (Nat.le_of_lt (hfl ▸ ha))
        rw [hzl, show ps ++ (mots ++ mins) ++ fsv ++ [] ++ zs = ps ++ mots ++ mins ++
            fsv ++ zs by simp]
          at hpullR
        let idxRv := idx.map (interp M (blev b ls) · (zs.reverse ++ pre ps.reverse fsv a))
        have hidxRv : (idx.map fun t => b.sh (place (b.nparams + a + xs.length)
            (b.σ2 a b.pre (b.pre + c.fields.length)) (b.pre + c.fields.length + xs.length) t)).map
            (interp (M₃ M b) ls · (ps ++ mots ++ mins ++ fsv ++ zs).reverse) = idxRv := by
          rw [List.map_map]
          apply List.map_congr_left
          intro t ht
          simp only [Function.comp]
          rw [interp_sh_place (M₃ M b) ls b _ _ _ t _ (hidxc t ht) hW2
            (fun L hL => by unfold SBlock.σ2; split; omega; split <;> omega), hpullR,
            interp_congr (S.free' hag (hidxR t ht).1 (hidxR t ht).2)]
          simp [pre]
        simp only [interp]
        rw [interp_appN, interp_appN, List.map_append, interp_vars _ _ hW2 (by omega),
          interp_var _ _ hW2 (by omega), interp_vars _ _ hW2 (by omega), hidxRv]
        have e0 : ((ps ++ mots ++ mins ++ fsv ++ zs).drop 0).take b.pre = ps ++ mots ++ mins := by
          simp only [List.drop_zero]
          rw [show ps ++ mots ++ mins ++ fsv ++ zs = (ps ++ mots ++ mins) ++ (fsv ++ zs) by simp,
            show b.pre = (ps ++ mots ++ mins).length by simp only [List.length_append]; omega,
            List.take_left]
        have ea : (ps ++ mots ++ mins ++ fsv ++ zs).getD (b.pre + a) pt = fsv.getD a pt := by
          rw [show ps ++ mots ++ mins ++ fsv ++ zs = (ps ++ mots ++ mins) ++ (fsv ++ zs) by simp,
            getD_append_right' (by simp only [List.length_append]; omega),
            show b.pre + a - (ps ++ mots ++ mins).length = a by
                simp only [List.length_append]; omega,
            getD_append_left' (by omega)]
        have ez : ((ps ++ mots ++ mins ++ fsv ++ zs).drop (b.pre + c.fields.length)).take
            xs.length = zs := by
          rw [show b.pre + c.fields.length = (ps ++ mots ++ mins ++ fsv).length by
            simp only [List.length_append]; omega, List.drop_left, ← hzl, List.take_length]
        rw [e0, ea, ez]
        have hmemU := recCall_mem_U hK hd hcq hfit (List.getElem?_eq_getElem ha) hcert' hzs
        have hmemP : recCall M (blev b ls) ps.reverse fsv a k idx zs ∈ˢ
            pred M (blev b ls) b ps.reverse (d, q, fsv) :=
          mem_pred.mpr ⟨c, a, c.fields[a], xs, k, idx, zs, hcq, List.getElem?_eq_getElem ha,
              hcert', hzs, rfl⟩
        rw [app_graph hmemP]
        unfold recCall at hmemU ⊢
        obtain ⟨k', _, i, hi', x', hx', heq⟩ := mem_unionSet.mp hmemU
        obtain ⟨hkk, hii, hxx⟩ := tagged_inj heq
        subst hkk hii hxx
        obtain ⟨zs', hzs', hti⟩ := (mem_extSet M _).mp hi'
        have hivR : Ext M (blev b ls) (b.types[k]!).indices ps.reverse idxRv := by
          have e := mkTower_inj_of_length hti (by rw [Ext.length_eq _ _ hzs']; simp [hidxlR])
          rw [show idxRv = zs' from e]; exact hzs'
        have hfold : ∀ (l : List V) (x y : V), app (l.foldl app x) y = (l ++ [y]).foldl app x :=
          fun l x y => by rw [List.foldl_append]; rfl
        rw [hfold]
        exact S.rec_call_eq h2 h3 hl hpre3 hps hmotl hminl hk hivR hx'
  · simp only [interp]
    rw [hintro, interp_appN, hidxv, interp_var _ _ hW (by omega)]
    have hmot' : (ps ++ mots ++ mins ++ fsv).getD (b.nparams + d) pt = mots.getD d pt := by
      simp only [List.append_assoc]
      rw [getD_append_right' (by omega), show b.nparams + d - ps.length = d by omega,
        getD_append_left' (by omega)]
    rw [hmot']
    have hrec := rec_mem hK hs hB hmot hmin huq hu
    unfold Bnd at hrec
    rw [untag_tagged] at hrec
    simp only [] at hrec
    rw [projList_mkTower _ _ (by simp [iv, nidx, hidxl])] at hrec
    exact hrec

theorem iota_law {d q : Nat} {c : SCtor} (hcq : (ctorsOf b d)[q]? = some c) (ls : List Nat)
    (hl : ls.length = b.recUvars) (ρ : List V) :
    interp (M₃ M b) ls (b.iota d q).lhs ρ = interp (M₃ M b) ls (b.iota d q).rhs ρ ∧
      interp (M₃ M b) ls (b.iota d q).lhs ρ ∈ˢ interp (M₃ M b) ls (b.iota d q).type ρ := by
  obtain ⟨hsl, hsr, hst⟩ := S.iota_scoped₃ h2 h3 hcq
  rw [interp_closed _ _ hsl.1 ρ, interp_closed _ _ hsr.1 ρ, interp_closed _ _ hst.1 ρ, iota_eq]
  simp only []
  rw [interp_lamTel', interp_lamTel', interp_forallTel]
  exact ⟨lamTel_congr fun ws hws => (S.iota_core h2 h3 hcq hl hws).1,
    lamTel_mem_piTel fun ws hws => (S.iota_core h2 h3 hcq hl hws).2⟩

end Setting
namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem model_add {env' : VEnv} (hadd : b.add env = some env') :
    IsModel (M₃ M b) env' ∧ Good env' := by
  obtain ⟨e₁, e₂, e₃, h1, h2, h3, rfl⟩ := add_spec hadd
  have he : e₁ = env₁ := Option.some.inj (h1.symm.trans S.hwt)
  subst he
  exact S.model_add_of_iota h2 h3 fun _ _ _ hcq ls hl ρ => S.iota_law h2 h3 hcq ls hl ρ

end Setting

end BlockModel
end Soulgem
