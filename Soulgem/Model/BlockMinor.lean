import Soulgem.Model.BlockMotive
import Soulgem.Model.BlockCtor

/-! # Minor premises -/

namespace Soulgem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V]

theorem IsModel.congr {M M' : CInterp V} {env : VEnv} (hM : IsModel M env) (hG : Good env)
    (h : ∀ c, Dom env c → M' c = M c) : IsModel M' env := by
  have hag : ∀ {e}, ConstsIn (Dom env) e → ∀ ls ρ, interp M' ls e ρ = interp M ls e ρ :=
    fun he _ ρ => interp_congr (he.mono h) ρ
  refine ⟨fun {c ci} hc ls hl ρ => ?_, fun {df} hdf ls hl ρ => ?_⟩
  · obtain ⟨_, hT, _⟩ := hG.2.1 hc
    rw [hag hT, h c (by simp [Dom, hc])]
    exact hM.const hc ls hl ρ
  · obtain ⟨⟨hl1, hT⟩, hr, _⟩ := hG.2.2 hdf
    rw [hag hl1, hag hr, hag hT]
    exact hM.defeq hdf ls hl ρ

theorem Sat.congrM' {M M' : CInterp V} {ls : List Nat} {P : Name → Prop}
    (hag : ∀ c, P c → M c = M' c) :
    ∀ {Γ : List VExpr} {ρ : List V}, (∀ A ∈ Γ, ConstsIn P A) → (Sat M ls Γ ρ ↔ Sat M' ls Γ ρ)
  | [], [], _ => Iff.rfl
  | [], _ :: _, _ => Iff.rfl
  | _ :: _, [], _ => Iff.rfl
  | A :: Γ, x :: ρ, h => by
    simp only [Sat]
    rw [Sat.congrM' hag fun B hB => h B (.tail _ hB),
      interp_congr ((h A (.head _)).mono hag)]

theorem recFields_mem {c : SCtor} {x : Nat × List VExpr × Nat × List VExpr} (hx : x ∈ c.recFields) :
    x.1 < c.fields.length ∧ (c.fields[x.1]!).cert = .recursive x.2.1 x.2.2.1 x.2.2.2 := by
  unfold SCtor.recFields at hx
  obtain ⟨a, ha, h⟩ := List.mem_filterMap.mp hx
  rw [List.mem_range] at ha
  split at h
  · rename_i xs k idx hcert; cases h; exact ⟨ha, hcert⟩
  · cases h

namespace BlockModel
open BlockSem

theorem pull_σ2 (b : SBlock) {ps mid fs mid2 zs : List V} (hp : ps.length = b.nparams)
    {a D E : Nat} (hD : ps.length + mid.length = D) (hE : D + fs.length + mid2.length = E)
    (ha : a ≤ fs.length) :
    ((List.range (b.nparams + a + zs.length)).map fun L =>
      (ps ++ mid ++ fs ++ mid2 ++ zs).getD (b.σ2 a D E L) pt) = ps ++ fs.take a ++ zs := by
  apply List.ext_getElem (by simp [hp, Nat.min_eq_left ha]; omega)
  intro L h1 h2
  simp only [List.getElem_map, List.getElem_range, SBlock.σ2]
  have h1' : L < b.nparams + a + zs.length := by simpa using h1
  rw [List.getD_eq_getElem?_getD]
  by_cases hL : L < b.nparams
  · have e : (ps ++ mid ++ fs ++ mid2 ++ zs)[L]? = ps[L]? := by
      simp only [List.append_assoc]; rw [List.getElem?_append_left (by omega)]
    have e2 : (ps ++ List.take a fs ++ zs)[L] = ps[L]'(by omega) := by
      simp only [List.append_assoc]; rw [List.getElem_append_left (by omega)]
    rw [ite_eq_left hL, e, e2, List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [ite_eq_right hL]
    by_cases hL2 : L < b.nparams + a
    · rw [ite_eq_left hL2, List.getElem_append_left (by simp [Nat.min_eq_left ha]; omega),
        List.getElem_append_right (by omega)]
      have e : L - b.nparams + D = (ps ++ mid).length + (L - b.nparams) := by simp; omega
      rw [e]
      simp only [List.append_assoc]
      rw [← List.append_assoc ps mid, List.getElem?_append_right (by simp),
        List.getElem?_append_left (by simp; omega)]
      simp only [List.length_append, Nat.add_sub_cancel_left]
      rw [List.getElem?_eq_getElem (by omega), List.getElem_take]
      simp [hp]
    · rw [ite_eq_right hL2, List.getElem_append_right (by simp [Nat.min_eq_left ha]; omega)]
      have e : L - (b.nparams + a) + E = (ps ++ mid ++ fs ++ mid2).length +
          (L - (b.nparams + a)) := by
        simp; omega
      rw [e, List.getElem?_append_right (by simp), Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem (by omega)]
      simp [hp, Nat.min_eq_left ha]

theorem ctorBase_add_lt {b : SBlock} {m q : Nat} {c : SCtor} (h : (ctorsOf b m)[q]? = some c) :
    b.ctorBase m + q < b.nctors := by
  have hm := lt_of_ctor h
  have hq : q < (b.types[m]!).ctors.length := (List.getElem?_eq_some_iff.mp h).1
  have hm' : m < (b.types.map (·.ctors.length)).length := by rw [List.length_map]; exact hm
  unfold SBlock.ctorBase SBlock.nctors SBlock.ctors
  rw [List.length_flatMap, List.map_take]
  have hs : (b.types.map (·.ctors.length)).sum = ((b.types.map (·.ctors.length)).take m).sum +
      ((b.types.map (·.ctors.length)).drop m).sum := by
    rw [← List.sum_append, List.take_append_drop]
  rw [hs, List.drop_eq_getElem_cons hm', List.sum_cons]
  have e : (b.types.map (·.ctors.length))[m] = (b.types[m]!).ctors.length := by
    rw [List.getElem_map, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hm]
    rfl
  rw [e]
  omega

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem fctx_closed {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors) :
    ∀ a ≤ c.fields.length, CtxClosed (fctx b c a) := by
  intro a ha
  have h := tel_closed (As := c.fields.map (·.ty)) S.good₁.1 S.params_ctx_closed
    (U := b.uvars) (fun i hi => by
      have hi' : i < c.fields.length := by simpa using hi
      have := (S.field_ok hj hc hi').1
      have e : c.fields[i]! = c.fields[i] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
      rw [e] at this
      have e2 : (c.fields.map (·.ty)).take i = (c.fields.take i).map (·.ty) := by
        rw [List.map_take]
      rw [e2]
      simp only [List.getElem_map]
      exact ⟨_, by simpa [fctx] using this⟩) a (by simpa using ha)
  simpa [fctx, List.map_take] using h

theorem ext_fields {M' : CInterp V} (hM' : IsModel M' env₁) {ls' : List Nat} {ps : List V}
    (hplen : ps.length = b.nparams) {j : Nat} (hj : j < b.ntypes) {c : SCtor}
    (hc : c ∈ (b.types[j]!).ctors) {mid : List V} {D : Nat} (hD : ps.length + mid.length = D)
    (hpsat : Sat M' (blev b ls') b.params.reverse ps.reverse) (zs : List V) :
    Ext M' ls' ((List.range c.fields.length).map fun a =>
        b.binder (place (b.nparams + a) (b.σ1 D) (D + a) (c.fields[a]!).ty))
            (ps ++ mid).reverse zs ↔
      Ext M' (blev b ls') (c.fields.map (·.ty)) ps.reverse zs := by
  refine ext_transfer (by simp) fun a ha ha' ys hys => ?_
  have ha2 : a < c.fields.length := by simpa using ha'
  have hya : ys.length = a := by
    rw [Ext.length_eq _ _ hys, List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt ha')
  have hrev : ys.reverse ++ (ps ++ mid).reverse = (ps ++ mid ++ ys).reverse := by simp
  rw [hrev]
  simp only [List.getElem_map, List.getElem_range]
  have hsat : Sat M' (blev b ls') (fctx b c a) (ps ++ ys).reverse := by
    have := Sat.of_ext hpsat hys
    simpa [fctx, List.map_take] using this
  rw [interp_binder_place hM' S.good₁.1 ls' b (S.fctx_closed hj hc a (Nat.le_of_lt ha2))
    (b.nparams + a) (by
        simp only [fctx, List.length_reverse, List.length_append, List.length_map, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt ha2)]; rfl)
    (b.σ1 D) (D + a) _ (S.field_ok hj hc ha2).2.1 (ps ++ mid ++ ys)
    (by simp only [List.length_append]; omega) (fun L hL => by unfold SBlock.σ1; split <;> omega)
    (by rw [pull_σ1 b hplen hD a hya]; exact hsat)]
  rw [pull_σ1 b hplen hD a hya, List.reverse_append]
  have e : c.fields[a]! = c.fields[a] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha2]; rfl
  rw [e]

theorem rec_field {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors)
    {a : Nat} (ha : a < c.fields.length) {xs : List VExpr} {k : Nat} {idx : List VExpr}
    (hcert : (c.fields[a]!).cert = .recursive xs k idx) :
    k < b.ntypes ∧ idx.length = (b.types[k]!).indices.length ∧
    (∀ x ∈ xs, ConstsIn (Dom env₁) x ∧ mentions b.names x = false) ∧
    (∀ i ∈ idx, ConstsIn (Dom env₁) i ∧ mentions b.names i = false) ∧
    (∀ e < xs.length, AnnOK env₁ b.uvars ((xs.take e).reverse ++ fctx b c a) xs[e]!) ∧
    (∀ e ≤ xs.length, CtxClosed ((xs.take e).reverse ++ fctx b c a)) ∧
    (∀ i ∈ idx, i.ClosedN (b.nparams + a + xs.length)) := by
  have hfok := S.field_full hj hc ha
  unfold Setting.FieldFull at hfok
  simp only [hcert] at hfok
  obtain ⟨hk, hidxl, ⟨_, hdty⟩, hxsm, hidxm, hann, hidxty, hsorts⟩ := hfok
  have hctx := S.fctx_consts hj hc a (Nat.le_of_lt ha)
  have hR := (IsDefEq.constsIn S.good₁.2 hdty hctx).2.1
  rw [constsIn_forallTel] at hR
  obtain ⟨hxs, hind⟩ := hR
  unfold SBlock.indApp at hind
  rw [constsIn_appN] at hind
  have hcl : ∀ e ≤ xs.length, CtxClosed ((xs.take e).reverse ++ fctx b c a) :=
    tel_closed S.good₁.1 (S.fctx_closed hj hc a (Nat.le_of_lt ha)) (U := b.uvars) fun e he => by
      obtain ⟨u, hu, _⟩ := hsorts e he
      have e' : xs[e]! = xs[e] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem he]; rfl
      rw [e'] at hu; exact ⟨u, hu⟩
  refine ⟨hk, hidxl, fun x hx => ⟨hxs x hx, hxsm x hx⟩,
    fun i hi => ⟨hind.2 i (List.mem_append_right _ hi), hidxm i hi⟩, hann, hcl, fun i hi => ?_⟩
  obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.mp hi
  have h := hidxty l hl
  have e' : idx[l]! = idx[l] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl
  rw [e'] at h
  have hcl' := hcl xs.length (Nat.le_refl _)
  rw [List.take_length] at hcl'
  have := (h.closedN' S.good₁.1 hcl').1
  have hlen : (xs.reverse ++ fctx b c a).length = b.nparams + a + xs.length := by
    simp only [fctx, List.length_append, List.length_reverse, List.length_map, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt ha)]
    show xs.length + (b.nparams + a) = b.nparams + a + xs.length
    omega
  rwa [hlen] at this

variable {M' : CInterp V} in
theorem free' (hag : ∀ x, Dom env₁ x → M' x = Mc M b x) {e : VExpr} (h₁ : ConstsIn (Dom env₁) e)
    (hm : mentions b.names e = false) : ConstsIn (fun x => M' x = M x) e :=
  (h₁.and (S.free (C := fun ls ρp => carrier M ls b ρp) h₁ hm)).mono fun x ⟨hd, he⟩ =>
    (hag x hd).trans he

theorem fields_sat {M' : CInterp V} (hag : ∀ x, Dom env₁ x → M' x = Mc M b x) {ls : List Nat}
    (hl : ls.length = b.uvars) {ps : List V} (hps : Ext M ls b.params [] ps) {j : Nat}
    (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors) {fs : List V}
    (hfit : FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fs) :
    Sat M' ls b.params.reverse ps.reverse ∧ Ext M' ls (c.fields.map (·.ty)) ps.reverse fs := by
  have hfl := hfit.length_eq
  have h := (S.ffit_iff_sat (carrier_tupleFn M b) hl hj hc hps c.fields.length (Nat.le_refl _) fs
    hfl).mp (by simpa using hfit)
  have hcons := S.fctx_consts hj hc c.fields.length (Nat.le_refl _)
  rw [Sat.congrM' (M' := M') (fun x hx => (hag x hx).symm) hcons] at h
  have h' : Sat M' ls ((c.fields.map (·.ty)).reverse ++ b.params.reverse)
      (fs.reverse ++ ps.reverse) := by
    simpa [fctx] using h
  exact Ext.of_sat (by simp [hfl]) h'

theorem ih_mem {M' : CInterp V} (hag : ∀ x, Dom env₁ x → M' x = Mc M b x) (hM' : IsModel M' env₁)
    {ls' : List Nat} {ps : List V} (hps : Ext M (blev b ls') b.params [] ps) {j : Nat}
    (hj : j < b.ntypes) {q : Nat} {c : SCtor} (hcq : (ctorsOf b j)[q]? = some c)
    {mots mid : List V} {D : Nat} (hD : ps.length + mid.length = D) (hmidl : b.ntypes ≤ mid.length)
    (hmid : ∀ k < b.ntypes, mid.getD k pt = mots.getD k pt) {fsv : List V}
    (hfit : FFit M (blev b ls') (carrier M (blev b ls') b ps.reverse) c.fields ps.reverse fsv)
    {g : V} (hg : g ∈ˢ piSet (pred M (blev b ls') b ps.reverse (j, q, fsv)) (Bnd b mots))
    {a : Nat} {xs : List VExpr} {k : Nat} {idx : List VExpr} (hR : (a, xs, k, idx) ∈ c.recFields)
    (ys : List V) {E : Nat} (hE : D + fsv.length + ys.length = E) :
    ihVal M (blev b ls') ps.reverse g fsv (a, xs, k, idx) ∈ˢ
      interp M' ls' (Spec.forallTel ((List.range xs.length).map fun e =>
          b.binder (place (b.nparams + a + e) (b.σ2 a D E) (E + e) xs[e]!))
        (.app (appN (var (E + xs.length) (b.nparams + k))
            (idx.map fun t => b.sh (place (b.nparams + a + xs.length) (b.σ2 a D E)
                (E + xs.length) t)))
          (appN (var (E + xs.length) (D + a)) (vars (E + xs.length) E xs.length))))
        (ps ++ mid ++ fsv ++ ys).reverse := by
  have hc : c ∈ (b.types[j]!).ctors := List.mem_of_getElem? hcq
  obtain ⟨ha, hcert⟩ := recFields_mem hR
  simp only at ha hcert
  obtain ⟨hk, hidxl, hxs, hidx, hann, hcl, hidxc⟩ := S.rec_field hj hc ha hcert
  have hl := blev_length b ls'
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hfl : fsv.length = c.fields.length := hfit.length_eq
  obtain ⟨hpS, hfE⟩ := S.fields_sat hag hl hps hj hc hfit
  have hsatA : Sat M' (blev b ls') (fctx b c a) (ps ++ fsv.take a).reverse := by
    have h1 := (Ext.split (As := (c.fields.map (·.ty)).take a) (Bs := (c.fields.map (·.ty)).drop a)
      (by rw [List.take_append_drop]; exact hfE)).1
    have h2 := Sat.of_ext hpS h1
    simpa [fctx, List.map_take, Nat.min_eq_left (Nat.le_of_lt ha)] using h2
  have hag' : ∀ e ∈ xs, ConstsIn (fun x => M x = M' x) e := fun e he =>
    (S.free' hag (hxs e he).1 (hxs e he).2).mono fun _ h => h.symm
  have hσ : ∀ e, ∀ L < b.nparams + a + e, b.σ2 a D E L < E + e := fun e L hL => by
    unfold SBlock.σ2; split
    · omega
    · split <;> omega
  rw [interp_forallTel]
  unfold ihVal
  simp only []
  have hcert' : (c.fields[a]).cert = .recursive xs k idx := by
    rw [← hcert, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha]; rfl
  rw [piTel_transfer (M₂ := M) (ls₂ := blev b ls') (Bs := xs) (ρ₂ := pre ps.reverse fsv a)
    (B₂ := fun ρ' => Bnd b mots
      (recCall M (blev b ls') ps.reverse fsv a k idx (ρ'.take xs.length).reverse))
    (by simp) (fun e he he' zs hzs => ?bind) fun zs hzs => ?body]
  · refine lamTel_mem_piTel fun zs hzs => ?_
    have hzl : zs.length = xs.length := Ext.length_eq _ _ hzs
    have htk : ((zs.reverse ++ pre ps.reverse fsv a).take xs.length).reverse = zs := by
      rw [List.take_append_of_le_length (by simp [hzl]), List.take_of_length_le (by simp [hzl]),
        List.reverse_reverse]
    simp only [htk]
    exact app_mem_of_mem_piSet hg (mem_pred.mpr ⟨c, a, c.fields[a], xs, k, idx, zs, hcq,
      List.getElem?_eq_getElem ha, hcert', hzs, rfl⟩)
  case bind =>
    have hze : zs.length = e := by
      rw [Ext.length_eq _ _ hzs, List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt he')
    have hrev : zs.reverse ++ (ps ++ mid ++ fsv ++ ys).reverse =
        (ps ++ mid ++ fsv ++ ys ++ zs).reverse := by
      simp
    rw [hrev]
    simp only [List.getElem_map, List.getElem_range]
    have hpull := pull_σ2 b (mid := mid) (fs := fsv) (mid2 := ys) (zs := zs) hplen hD hE
      (Nat.le_of_lt (hfl ▸ ha))
    rw [hze] at hpull
    have hzs' : Ext M' (blev b ls') (xs.take e) (ps ++ fsv.take a).reverse zs := by
      have := (Ext.congrM (fun _ h => h) fun A hA => hag' A (List.mem_of_mem_take hA)).mp hzs
      simpa [pre] using this
    rw [interp_binder_place hM' S.good₁.1 ls' b (hcl e (Nat.le_of_lt he')) (b.nparams + a + e)
      (by simp only [fctx, List.length_append, List.length_reverse, List.length_map,
          List.length_take, Nat.min_eq_left (Nat.le_of_lt ha), Nat.min_eq_left (Nat.le_of_lt he')]
          show e + (b.nparams + a) = b.nparams + a + e; omega)
      (b.σ2 a D E) (E + e) _ (hann e he') (ps ++ mid ++ fsv ++ ys ++ zs)
      (by simp only [List.length_append]; omega) (hσ e)
      (by rw [hpull]; have := Sat.of_ext hsatA hzs'; simpa using this)]
    rw [hpull]
    have e' : xs[e]! = xs[e] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem he']; rfl
    rw [e', interp_congr (S.free' hag (hxs _ (List.getElem_mem he')).1
      (hxs _ (List.getElem_mem he')).2)]
    simp [pre]
  case body =>
    have hzl : zs.length = xs.length := Ext.length_eq _ _ hzs
    have htk : ((zs.reverse ++ pre ps.reverse fsv a).take xs.length).reverse = zs := by
      rw [List.take_append_of_le_length (by simp [hzl]), List.take_of_length_le (by simp [hzl]),
        List.reverse_reverse]
    simp only [htk]
    have hrev : zs.reverse ++ (ps ++ mid ++ fsv ++ ys).reverse =
        (ps ++ mid ++ fsv ++ ys ++ zs).reverse := by
      simp
    rw [hrev]
    have hW : (ps ++ mid ++ fsv ++ ys ++ zs).length = E + xs.length := by
      simp only [List.length_append]; omega
    have hpull := pull_σ2 b (mid := mid) (fs := fsv) (mid2 := ys) (zs := zs) hplen hD hE
      (Nat.le_of_lt (hfl ▸ ha))
    rw [hzl] at hpull
    simp only [interp]
    rw [interp_appN, interp_appN, interp_var _ _ hW (by omega), interp_var _ _ hW (by omega),
      interp_vars _ _ hW (by omega)]
    unfold recCall Bnd
    rw [untag_tagged]
    simp only []
    rw [projList_mkTower _ _ (by simp [nidx, hidxl])]
    have hdrop : ((ps ++ mid ++ fsv ++ ys ++ zs).drop E).take xs.length = zs := by
      rw [show E = (ps ++ mid ++ fsv ++ ys).length by simp only [List.length_append]; omega,
        List.drop_left, ← hzl, List.take_length]
    have hmot : (ps ++ mid ++ fsv ++ ys ++ zs).getD (b.nparams + k) pt = mots.getD k pt := by
      simp only [List.append_assoc]
      rw [getD_append_right' (by omega), show b.nparams + k - ps.length = k by omega,
        getD_append_left' (by omega), hmid k hk]
    have hfld : (ps ++ mid ++ fsv ++ ys ++ zs).getD (D + a) pt = fsv.getD a pt := by
      rw [show ps ++ mid ++ fsv ++ ys ++ zs = (ps ++ mid) ++ (fsv ++ (ys ++ zs)) by simp,
        getD_append_right' (by simp; omega), show D + a - (ps ++ mid).length = a by simp; omega,
        getD_append_left' (by omega)]
    rw [hdrop, hmot, hfld, List.map_map]
    congr 2
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp]
    rw [interp_sh_place M' ls' b _ _ _ t _ (hidxc t ht) hW (hσ xs.length), hpull,
      interp_congr (S.free' hag (hidx t ht).1 (hidx t ht).2)]
    simp [pre]

theorem ctor_idx {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors) :
    c.idx.length = (b.types[j]!).indices.length ∧
    ∀ t ∈ c.idx, t.ClosedN (b.nparams + c.fields.length) ∧ ConstsIn (Dom env₁) t ∧
      mentions b.names t = false := by
  have hidxl := (S.ctorSyn hj hc).idx_len
  have hidxm := (S.ctorSyn hj hc).idx_free
  have hidxty := (S.ctorOK j hj c hc).idx_typed
  have hctx := S.fctx_consts hj hc c.fields.length (Nat.le_refl _)
  have hcl := S.fctx_closed hj hc c.fields.length (Nat.le_refl _)
  have hfctx : fctx b c c.fields.length = (b.params ++ c.fields.map (·.ty)).reverse := by
    simp [fctx]
  refine ⟨hidxl, fun t ht => ?_⟩
  obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.mp ht
  have h := hidxty l hl
  have e : c.idx[l]! = c.idx[l] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl
  rw [e, ← hfctx] at h
  have hlen : (fctx b c c.fields.length).length = b.nparams + c.fields.length := by
    simp [fctx]; exact Nat.add_comm _ _
  refine ⟨?_, (IsDefEq.constsIn S.good₁.2 h hctx).1, hidxm _ ht⟩
  have := (h.closedN' S.good₁.1 hcl).1
  rwa [hlen] at this

theorem minor_apply {M' : CInterp V} (hag : ∀ x, Dom env₁ x → M' x = Mc M b x)
    (hM' : IsModel M' env₁) {ls' : List Nat} {ps : List V} (hps : Ext M (blev b ls') b.params [] ps)
    {j : Nat} (hj : j < b.ntypes) {q : Nat} {c : SCtor} (hcq : (ctorsOf b j)[q]? = some c)
    (hctor : M' c.name = fun ls => ctorVal b (Mc M b) ls q c)
    {mots mid : List V} {D : Nat} (hD : ps.length + mid.length = D) (hmidl : b.ntypes ≤ mid.length)
    (hmid : ∀ k < b.ntypes, mid.getD k pt = mots.getD k pt) {fsv : List V}
    (hfit : FFit M (blev b ls') (carrier M (blev b ls') b ps.reverse) c.fields ps.reverse fsv)
    {g : V} (hg : g ∈ˢ piSet (pred M (blev b ls') b ps.reverse (j, q, fsv)) (Bnd b mots))
    {mn : V} (hmn : mn ∈ˢ interp M' ls' (b.minorTy j c D) (ps ++ mid).reverse) :
    (fsv ++ c.recFields.map (ihVal M (blev b ls') ps.reverse g fsv)).foldl app mn ∈ˢ
      Bnd b mots (tagged j (cidx M (blev b ls') ps.reverse c fsv) (enc (blev b ls') b q fsv)) := by
  have hc : c ∈ (b.types[j]!).ctors := List.mem_of_getElem? hcq
  have hl := blev_length b ls'
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hfl : fsv.length = c.fields.length := hfit.length_eq
  obtain ⟨hpS, hfE⟩ := S.fields_sat hag hl hps hj hc hfit
  obtain ⟨hidxl, hidx⟩ := S.ctor_idx hj hc
  let R := c.recFields
  let ihv := R.map (ihVal M (blev b ls') ps.reverse g fsv)
  unfold SBlock.minorTy at hmn
  simp only [] at hmn
  rw [interp_forallTel] at hmn
  have hEF := (S.ext_fields hM' hplen hj hc hD hpS fsv).mpr hfE
  have hEI : Ext M' ls' ((List.range R.length).map fun r =>
      let (a, xs, k, idx) := R[r]!
      let E := D + c.fields.length + r
      let nx := xs.length
      let xsP := (List.range nx).map fun e =>
        b.binder (place (b.nparams + a + e) (b.σ2 a D E) (E + e) xs[e]!)
      let d := E + nx
      let idxP := idx.map fun t => b.sh (place (b.nparams + a + nx) (b.σ2 a D E) d t)
      Spec.forallTel xsP (.app (appN (var d (b.nparams + k)) idxP)
        (appN (var d (D + a)) (vars d E nx))))
      (fsv.reverse ++ (ps ++ mid).reverse) ihv := by
    refine Ext.of_get (by simp [ihv]) fun r h1 h2 => ?_
    have hr : r < R.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, ihv]
    have hR : R[r]! = R[r] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hr]; rfl
    rw [hR]
    rcases hx : R[r] with ⟨a, xs, k, idx⟩
    have hmem : (a, xs, k, idx) ∈ c.recFields := hx ▸ List.getElem_mem hr
    have htk : ((R.map (ihVal M (blev b ls') ps.reverse g fsv)).take r).length = r := by
      simp; omega
    have hrev : ((R.map (ihVal M (blev b ls') ps.reverse g fsv)).take r).reverse ++
        (fsv.reverse ++ (ps ++ mid).reverse) =
        (ps ++ mid ++ fsv ++ (R.map (ihVal M (blev b ls') ps.reverse g fsv)).take r).reverse := by
      simp
    simp only []
    rw [hrev]
    exact S.ih_mem hag hM' hps hj hcq hD hmidl hmid hfit hg hmem _ (by rw [htk, hfl])
  have h := apps_mem_piTel hmn (Ext.append hEF hEI)
  have hW : (ps ++ mid ++ fsv ++ ihv).length = D + c.fields.length + R.length := by
    simp only [List.length_append, List.length_map, ihv]; omega
  have hrev : (fsv ++ ihv).reverse ++ (ps ++ mid).reverse = (ps ++ mid ++ fsv ++ ihv).reverse := by
    simp
  rw [hrev] at h
  simp only [interp] at h
  rw [interp_appN, interp_appN, interp_var _ _ hW (by omega), List.map_append,
    interp_vars _ _ hW (by omega), interp_vars _ _ hW (by omega)] at h
  have hmot : (ps ++ mid ++ fsv ++ ihv).getD (b.nparams + j) pt = mots.getD j pt := by
    simp only [List.append_assoc]
    rw [getD_append_right' (by omega), show b.nparams + j - ps.length = j by omega,
      getD_append_left' (by omega), hmid j hj]
  have hd0 : ((ps ++ mid ++ fsv ++ ihv).drop 0).take b.nparams = ps := by
    simp [hplen]
  have hdD : ((ps ++ mid ++ fsv ++ ihv).drop D).take c.fields.length = fsv := by
    rw [show D = (ps ++ mid).length by simp; omega,
      show ps ++ mid ++ fsv ++ ihv = (ps ++ mid) ++ (fsv ++ ihv) by simp, List.drop_left, ← hfl,
      List.take_left]
  rw [hmot, hd0, hdD] at h
  simp only [interp, hctor] at h
  have hpsc : Ext (Mc M b) (blev b ls') b.params [] ps :=
    (Ext.congrM (M := M) (M' := Mc M b) (fun _ h => h) fun A hA =>
      (S.free₀ (S.params_consts' A hA)).mono fun _ h => h.symm).mp hps
  have hfsc : Ext (Mc M b) (blev b ls') (c.fields.map (·.ty)) ps.reverse fsv := by
    refine (Ext.congrM (M := M') (M' := Mc M b) (fun x hx => hag x hx) fun A hA => ?_).mp hfE
    exact S.fctx_consts hj hc c.fields.length (Nat.le_refl _) A
        (by simp only [fctx, List.take_length, List.mem_reverse, List.mem_append]; exact .inr hA)
  have hval : (ps ++ fsv).foldl app (ctorVal b (Mc M b) (blev b ls') q c) =
      enc (blev b ls') b q fsv := by
    unfold ctorVal
    rw [List.foldl_append, apps_lamTel hpsc]
    simp only [List.append_nil]
    rw [apps_lamTel hfsc]
    have htk : (fsv.reverse ++ ps.reverse).take c.fields.length = fsv.reverse :=
      (List.take_append_of_le_length (by simp [hfl])).trans (List.take_of_length_le (by simp [hfl]))
    rw [htk, List.reverse_reverse]
  have hval' : List.foldl app (ctorVal b (Mc M b) (List.map (VLevel.eval ls') b.blockLevels) q c)
      (ps ++ fsv) = enc (blev b ls') b q fsv := hval
  rw [hval'] at h
  have hidx' : ((c.idx.map fun t => b.sh (place (b.nparams + c.fields.length) (b.σ1 D)
      (D + c.fields.length + c.recFields.length) t)).map fun x =>
        interp M' ls' x (ps ++ mid ++ fsv ++ ihv).reverse) =
      c.idx.map (interp M (blev b ls') · (fsv.reverse ++ ps.reverse)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    obtain ⟨htc, htd, htm⟩ := hidx t ht
    simp only [Function.comp]
    rw [interp_sh_place M' ls' b _ _ _ t _ htc hW (fun L hL =>
        by unfold SBlock.σ1; split <;> omega)]
    have hpull : ((List.range (b.nparams + c.fields.length)).map fun L =>
        (ps ++ mid ++ fsv ++ ihv).getD (b.σ1 D L) pt) = ps ++ fsv := by
      rw [← pull_σ1 b hplen hD c.fields.length hfl]
      apply List.map_congr_left
      intro L hL
      rw [List.mem_range] at hL
      exact getD_append_left' (by simp only [List.length_append]; unfold SBlock.σ1; split <;> omega)
    rw [hpull, interp_congr (S.free' hag htd htm), List.reverse_append]
  rw [hidx'] at h
  unfold Bnd cidx
  rw [untag_tagged]
  simp only []
  rw [projList_mkTower _ _ (by simp [nidx, hidxl])]
  exact h

theorem hMin {M' : CInterp V} (hag : ∀ x, Dom env₁ x → M' x = Mc M b x) (hM' : IsModel M' env₁)
    (hctor : ∀ j < b.ntypes, ∀ q c, (ctorsOf b j)[q]? = some c →
      M' c.name = fun ls => ctorVal b (Mc M b) ls q c)
    {ls' : List Nat} {ps : List V} (hps : Ext M (blev b ls') b.params [] ps)
    {mots mins : List V} (hmotl : mots.length = b.ntypes) (hminl : b.nctors ≤ mins.length)
    (hmins : ∀ j < b.ntypes, ∀ q c, (ctorsOf b j)[q]? = some c →
      mins.getD (b.ctorBase j + q) pt ∈ˢ interp M' ls'
        (b.minorTy j c (b.nparams + b.ntypes + b.ctorBase j + q))
        (ps ++ mots ++ mins.take (b.ctorBase j + q)).reverse) :
    HMin M (blev b ls') b ps.reverse mots mins := by
  intro u d hd g hg
  obtain ⟨m, q, fsv⟩ := d
  obtain ⟨i, _, ⟨c, hc, hfit, rfl⟩, rfl⟩ := hd
  simp only at hc hfit hg ⊢
  have hm := lt_of_ctor hc
  have hlt := ctorBase_add_lt hc
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  unfold st
  simp only [hc]
  exact S.minor_apply hag hM' hps hm hc (hctor m hm q c hc)
    (mid := mots ++ mins.take (b.ctorBase m + q)) (D := b.nparams + b.ntypes + b.ctorBase m + q)
    (by simp only [List.length_append, List.length_take, hplen, hmotl]; omega)
    (by simp only [List.length_append, hmotl]; omega)
    (fun k hk => getD_append_left' (by omega)) hfit hg
    (by rw [← List.append_assoc]; exact hmins m hm q c hc)

end Setting
end BlockModel
end Soulgem
