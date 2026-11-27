import Soulgem.Model.BlockSize

/-! # The operator's bound hypothesis `HBound` -/

namespace Soulgem.BlockModel
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem

universe u
variable {V : Type u} [SetTheory V]

/-! ## Generic lemmas -/

theorem pt_mem_cpi {A : V} {B : V → V} (h : ∀ x, x ∈ˢ A → pt ∈ˢ B x) : (pt : V) ∈ˢ cpi A B := by
  have e : clam A (fun _ => (pt : V)) = pt := by simp [clam]
  rw [← e]; exact clam_mem_cpi h

theorem pt_mem_piTel {M : CInterp V} {ls : List Nat} {B : List V → V} :
    ∀ {As : List VExpr} {ρ : List V}, (∀ ys, Ext M ls As ρ ys → pt ∈ˢ B (ys.reverse ++ ρ)) →
    (pt : V) ∈ˢ piTel M ls As B ρ
  | [], ρ, h => h [] .nil
  | A :: As, ρ, h => by
    simp only [piTel]
    refine pt_mem_cpi fun x hx => pt_mem_piTel fun ys hys => ?_
    have := h (x :: ys) (.cons hx hys)
    simpa using this

theorem telOf_congr {M : CInterp V} {ls : List Nat} :
    ∀ {As : List VExpr} {ρ ρ' : List V},
    (∀ e (he : e < As.length), ∀ ys : List V, ys.length = e →
      interp M ls As[e] (ys.reverse ++ ρ) = interp M ls As[e] (ys.reverse ++ ρ')) →
    telOf M ls As ρ = telOf M ls As ρ'
  | [], _, _, _ => rfl
  | A :: As, ρ, ρ', h => by
    simp only [telOf]
    have h0 := h 0 (by simp) [] rfl
    simp only [List.reverse_nil, List.nil_append, List.getElem_cons_zero] at h0
    rw [h0]
    congr 1; funext x
    refine telOf_congr fun e he ys hys => ?_
    have := h (e + 1) (by simp; omega) (x :: ys) (by simp [hys])
    simpa using this

theorem extSet_congr {M : CInterp V} {ls : List Nat} {As : List VExpr} {ρ ρ' : List V}
    (h : ∀ e (he : e < As.length), ∀ ys : List V, ys.length = e →
      interp M ls As[e] (ys.reverse ++ ρ) = interp M ls As[e] (ys.reverse ++ ρ')) :
    extSet M ls As ρ = extSet M ls As ρ' := by
  unfold extSet; rw [telOf_congr h]

theorem boundS_telOf {M : CInterp V} {ls : List Nat} {w : Nat} :
    ∀ {As : List VExpr} {ρ : List V},
    (∀ e (he : e < As.length), ∀ ys, Ext M ls (As.take e) ρ ys →
      interp M ls As[e] (ys.reverse ++ ρ) ∈ˢ (univ w : V)) →
    BoundS w (telOf M ls As ρ)
  | [], _, _ => trivial
  | A :: As, ρ, h => by
    refine ⟨h 0 (by simp) [] .nil, fun x hx => boundS_telOf fun e he ys hys => ?_⟩
    have := h (e + 1) (by simp; omega) (x :: ys) (by simpa using Ext.cons hx hys)
    simpa using this

theorem towerSet_pos_eq {w w' : Nat} (hw : w ≠ 0) (hw' : w' ≠ 0) {n : Nat} (T : TeleS V n) :
    towerSet w T = towerSet w' T :=
  SetTheory.ext fun _ => by rw [mem_towerSet_pos hw, mem_towerSet_pos hw']

theorem extSet_mem_univ {M : CInterp V} {ls : List Nat} {w : Nat} (hw : w ≠ 0)
    {As : List VExpr} {ρ : List V} (h : BoundS w (telOf M ls As ρ)) :
    extSet M ls As ρ ∈ˢ (univ w : V) := by
  unfold extSet; rw [towerSet_pos_eq Nat.one_ne_zero hw]; exact towerSet_mem_univ _ h

/-! ## `recIndep`, unpacked -/

theorem recIndep_spec {c : SCtor} (h : c.recIndep = true) {a₀ a' : Nat}
    (ha₀ : a₀ < c.fields.length) (ha' : a' < c.fields.length) (hlt : a₀ < a')
    {xs₀ : List VExpr} {k₀ : Nat} {idx₀ : List VExpr}
    (hrec : (c.fields[a₀]!).cert = .recursive xs₀ k₀ idx₀) :
    (∀ w, (c.fields[a']!).cert = .plain w → SBlock.hasVar w (a' - a₀ - 1) = false) ∧
    (∀ xs k idx, (c.fields[a']!).cert = .recursive xs k idx →
      ∀ e < xs.length, SBlock.hasVar xs[e]! (a' - a₀ - 1 + e) = false) := by
  simp only [SCtor.recIndep, List.all_eq_true, List.mem_range] at h
  have h1 := h a₀ ha₀
  rw [hrec] at h1
  simp only [List.all_eq_true, List.mem_range] at h1
  have h2 := h1 a' ha'
  have hnle : (a' ≤ a₀) = False := by simp; omega
  simp only [hnle, decide_false, Bool.false_or] at h2
  refine ⟨fun w hw => ?_, fun xs k idx hx e he => ?_⟩
  · rw [hw] at h2; simpa using h2
  · rw [hx] at h2; simp only [List.all_eq_true, List.mem_range] at h2
    simpa using h2 e he

theorem interp_agree_fields {M : CInterp V} {ls : List Nat} {c : SCtor} {a d : Nat}
    {fs fs' : List V} (hfs : fs.length = a) (hfs' : fs'.length = a) {ρp : List V}
    (hag : ∀ i < a, (∃ w, (c.fields[i]!).cert = .plain w) → fs.getD i pt = fs'.getD i pt)
    (e : VExpr)
    (hno : ∀ i < a, (∃ xs k idx, (c.fields[i]!).cert = .recursive xs k idx) →
      SBlock.hasVar e (a - i - 1 + d) = false)
    (ys : List V) (hys : ys.length = d) :
    interp M ls e (ys.reverse ++ (fs.reverse ++ ρp)) = interp M ls e
        (ys.reverse ++ (fs'.reverse ++ ρp)) := by
  refine interp_eq_of_agree e fun p hp => ?_
  by_cases hpd : p < d
  · rw [getD_append_left' (by simpa [hys] using hpd), getD_append_left' (by simpa [hys] using hpd)]
  · have hpd' : ys.reverse.length ≤ p := by simp [hys]; omega
    rw [getD_append_right' hpd', getD_append_right' hpd']
    simp only [List.length_reverse, hys]
    by_cases hpa : p - d < a
    · rw [getD_append_reverse (by omega), getD_append_reverse (by omega), hfs, hfs']
      have hi : a - 1 - (p - d) < a := by omega
      rcases hcert : (c.fields[a - 1 - (p - d)]!).cert with w | ⟨xs, k, idx⟩
      · exact hag _ hi ⟨w, hcert⟩
      · have := hno _ hi ⟨xs, k, idx, hcert⟩
        have e' : a - (a - 1 - (p - d)) - 1 + d = p := by omega
        rw [e', hp] at this; exact absurd this (by simp)
    · have h1 : fs.reverse.length ≤ p - d := by simp [hfs]; omega
      have h2 : fs'.reverse.length ≤ p - d := by simp [hfs']; omega
      rw [getD_append_right' h1, getD_append_right' h2]
      simp [hfs, hfs']

/-! ## The unit tuple -/

variable (M : CInterp V) (ls : List Nat) (b : SBlock) (ρp : List V) in
noncomputable def unitTuple : Nat → V := fun k => graph (fun _ => unitSet) (Is M ls b ρp k)

theorem unitTuple_space {M : CInterp V} {ls : List Nat} {b : SBlock} {ρp : List V} {w : Nat} :
    InTupleSpace w b.ntypes (Is M ls b ρp) (unitTuple M ls b ρp) :=
  fun _ _ => graph_mem_famSpace fun _ _ => unitSet_mem_univ _

theorem app_unitTuple {M : CInterp V} {ls : List Nat} {b : SBlock} {ρp : List V} {k : Nat} {i : V}
    (h : i ∈ˢ Is M ls b ρp k) : app (unitTuple M ls b ρp k) i = unitSet := app_graph h

variable (M : CInterp V) (ls : List Nat) (b : SBlock) (ρp : List V) in
noncomputable def piece (m q a : Nat) : V :=
  if m < b.ntypes then
    match (ctorsOf b m)[q]? with
    | some c => match c.fields[a]? with
      | some f => match f.cert with
        | .recursive xs _ _ => sUnion (image (fun t => extSet M ls xs
            ((projList a t).reverse ++ ρp))
            (towerSet (lev ls b) (telF M ls (unitTuple M ls b ρp) (c.fields.take a) ρp)))
        | .plain _ => empty
      | none => empty
    | none => empty
  else empty

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

omit [SetTheory V] S in
theorem getElem!_fields {c : SCtor} {a : Nat} (ha : a < c.fields.length) :
    c.fields[a]! = c.fields[a] := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha]; rfl

theorem bound_take {ls : List Nat} (hl : ls.length = b.uvars) {ps : List V}
    (hps : Ext M ls b.params [] ps) (h0 : lev ls b ≠ 0) {X : Nat → V}
    (hX : InTupleSpace (lev ls b) b.ntypes (Is M ls b ps.reverse) X)
    {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors)
    {n : Nat} (hn : n ≤ c.fields.length) :
    BoundS (lev ls b) (telF M ls X (c.fields.take n) ps.reverse) := by
  have key : ∀ r a, a + r = n → ∀ fs : List V, fs.length = a →
      FFit M ls X (c.fields.take a) ps.reverse fs →
      BoundS (lev ls b) (telF M ls X ((c.fields.take n).drop a) (fs.reverse ++ ps.reverse)) := by
    intro r
    induction r with
    | zero =>
      intro a ha fs _ _
      rw [List.drop_eq_nil_of_le (by simp; omega)]; trivial
    | succ r ih =>
      intro a ha fs hfs hfit
      have hlt : a < c.fields.length := by omega
      have hlt' : a < (c.fields.take n).length := by simp; omega
      rw [List.drop_eq_getElem_cons hlt', List.getElem_take]
      refine ⟨?_, fun x hx => ?_⟩
      · have := S.fdom_mem hl hps hX hj hc hlt hfs hfit
        rw [BlockModel.Setting.getElem!_fields hlt] at this
        exact univ_mono (BlockModel.Setting.getElem!_fields hlt ▸ S.sort_le h0 hj hc hlt) _ this
      · have h' := ih (a + 1) (by omega) (fs ++ [x]) (by simp [hfs])
          (by
            rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
              FFit.append (by simp [hfs, Nat.min_eq_left (Nat.le_of_lt hlt)]), FFit.single]
            exact ⟨hfit, hx⟩)
        simpa using h'
  exact key n 0 (by simp) [] rfl .nil

theorem idx_mem_Is {C : List Nat → List V → Nat → V} (hC : TupleFn M b C) {ls : List Nat}
    (_hl : ls.length = b.uvars) {j : Nat} (hj : j < b.ntypes)
    {c : SCtor} (hc : c ∈ (b.types[j]!).ctors) {a : Nat} (ha : a < c.fields.length)
    {xs : List VExpr} {k : Nat} {idx : List VExpr}
    (hcert : (c.fields[a]!).cert = .recursive xs k idx)
    {zs : List V} (hzl : zs.length = b.nparams + a)
    (hsat : Sat (M₁ M b C) ls (fctx b c a) zs.reverse)
    (_hps : Ext M ls b.params [] (zs.take b.nparams)) {ys : List V}
    (hys : Ext M ls xs zs.reverse ys) :
    mkTower (idx.map (interp M ls · (ys.reverse ++ zs.reverse))) ∈ˢ
      Is M ls b (zs.take b.nparams).reverse k := by
  have hfok := S.field_full hj hc ha
  have hM₁ := (S.model₁ hC).1
  have hctx := S.fctx_consts hj hc a (Nat.le_of_lt ha)
  unfold Setting.FieldFull at hfok
  simp only [hcert] at hfok
  obtain ⟨hk, hil, ⟨_, hd⟩, hxs, hidx, _, hty, _⟩ := hfok
  have hcR := (constsIn_forallTel xs _).mp (IsDefEq.constsIn S.good₁.2 hd hctx).2.1
  have hxfree : ∀ A ∈ xs, ConstsIn (fun c => M₁ M b C c = M c) A :=
    fun A hA => S.free (hcR.1 A hA) (hxs A hA)
  have hys₁ : Ext (M₁ M b C) ls xs zs.reverse ys :=
    (Ext.congrM (fun _ h => h) fun A hA => (hxfree A hA).mono fun _ h => h.symm).mp hys
  have hlen := Ext.length_eq M ls hys
  have hrev : ys.reverse ++ zs.reverse = (zs ++ ys).reverse := by simp
  have htake : (zs ++ ys).take b.nparams = zs.take b.nparams :=
    List.take_append_of_le_length (by omega)
  have hsat' : Sat (M₁ M b C) ls (xs.reverse ++ fctx b c a) (zs ++ ys).reverse := by
    rw [← hrev]; exact Sat.of_ext hsat hys₁
  have hfit := BlockModel.idx_fit_gen (M := M) hM₁ hsat' (n := b.nparams) (E := a + xs.length)
    (by simp [hzl, hlen]; omega) hil
    (fun l hl' => by
      have := hty l hl'
      rw [idxType_eq] at this
      simpa [Nat.add_sub_cancel_left] using this)
    (fun l hl' => S.indices_closed hk hl') (fun A hA => S.free₀ (S.indices_consts hk A hA))
  rw [htake] at hfit
  have hci : ∀ i ∈ idx, ConstsIn (Dom env₁) i := fun i hi =>
    ((constsIn_appN _ _).mp hcR.2).2 i (List.mem_append_right _ hi)
  have e : idx.map (interp (M₁ M b C) ls · (zs ++ ys).reverse) =
      idx.map (interp M ls · (ys.reverse ++ zs.reverse)) := by
    rw [hrev]; exact List.map_congr_left fun i hi => interp_congr (S.free (hci i hi) (hidx i hi)) _
  rw [e] at hfit
  exact mkTower_mem_extSet M ls hfit

theorem erase_fit {ls : List Nat} (hl : ls.length = b.uvars) {ps : List V}
    (hps : Ext M ls b.params [] ps) {X : Nat → V}
    {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors) :
    ∀ a ≤ c.fields.length, ∀ fs : List V, fs.length = a →
      FFit M ls X (c.fields.take a) ps.reverse fs →
      ∃ fs' : List V, fs'.length = a ∧
        FFit M ls (unitTuple M ls b ps.reverse) (c.fields.take a) ps.reverse fs' ∧
        ∀ i < a, (∃ w, (c.fields[i]!).cert = .plain w) → fs.getD i pt = fs'.getD i pt := by
  have hri := (S.ctorSyn hj hc).recIndep
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M ls hps]; rfl
  intro a
  induction a with
  | zero =>
    intro _ fs hfs _
    exact ⟨[], rfl, .nil, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ a ih =>
    intro ha fs hfs hfit
    have hlt : a < c.fields.length := by omega
    obtain ⟨fs₀, x, rfl⟩ : ∃ fs₀ x, fs = fs₀ ++ [x] := by
      refine ⟨fs.take a, fs[a]'(by omega), ?_⟩
      conv => lhs; rw [← List.take_append_drop a fs]
      congr 1
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
    have hfs₀ : fs₀.length = a := by simpa using hfs
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      FFit.append (by simp [hfs₀, Nat.min_eq_left (Nat.le_of_lt hlt)]), FFit.single] at hfit
    obtain ⟨hfit₀, hx⟩ := hfit
    obtain ⟨fs₀', hl₀', hfit₀', hag⟩ := ih (by omega) fs₀ hfs₀ hfit₀
    have hU := patch_tupleFn (M := M) (b := b) (ls₀ := ls) (ρ₀ := ps.reverse)
      (unitTuple_space (w := lev ls b))
    have hsat := (S.ffit_iff_sat hU hl hj hc hps a (Nat.le_of_lt hlt) fs₀' hl₀').mp
      (by rw [patch_at]; exact hfit₀')
    have step : ∃ x', x' ∈ˢ fdom M ls (unitTuple M ls b ps.reverse) c.fields[a]
          (fs₀'.reverse ++ ps.reverse) ∧ ((∃ w, (c.fields[a]!).cert = .plain w) → x = x') := by
      rcases hcert : (c.fields[a]!).cert with w | ⟨xs, k, idx⟩
      · refine ⟨x, ?_, fun _ => rfl⟩
        have hcert' := hcert
        rw [BlockModel.Setting.getElem!_fields hlt] at hcert'
        unfold fdom at hx ⊢; simp only [hcert'] at hx ⊢
        have e := interp_agree_fields (M := M) (ls := ls) (c := c) (d := 0) hfs₀ hl₀'
          (ρp := ps.reverse) hag w (fun i hi ⟨xs₀, k₀, idx₀, hr⟩ => by
            have := (recIndep_spec hri (by omega) hlt hi hr).1 w hcert
            simpa using this) [] rfl
        simp only [List.reverse_nil, List.nil_append] at e
        rw [← e]; exact hx
      · refine ⟨pt, ?_, fun ⟨w, hw⟩ => by cases hw⟩
        have hcert' := hcert
        rw [BlockModel.Setting.getElem!_fields hlt] at hcert'
        unfold fdom; simp only [hcert']
        refine pt_mem_piTel fun ys hys => ?_
        have hmem := S.idx_mem_Is hU hl hj hc hlt hcert (zs := ps ++ fs₀') (by simp [hplen, hl₀'])
          (by simpa using hsat) (by rw [List.take_append_of_le_length (by omega),
            List.take_of_length_le (by omega)]; exact hps) (ys := ys) (by simpa using hys)
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at hmem
        simp only [List.reverse_append] at hmem
        rw [app_unitTuple hmem]; exact pt_mem_unitSet
    obtain ⟨x', hx', hxx⟩ := step
    refine ⟨fs₀' ++ [x'], by simp [hl₀'], ?_, fun i hi hp => ?_⟩
    · rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
        FFit.append (by simp [hl₀', Nat.min_eq_left (Nat.le_of_lt hlt)]), FFit.single]
      exact ⟨hfit₀', hx'⟩
    · by_cases hia : i < a
      · rw [getD_append_left' (by omega), getD_append_left' (by omega)]; exact hag i hia hp
      · have hia' : i = a := by omega
        subst hia'
        rw [getD_append_right' (by omega), getD_append_right' (by omega), hfs₀, hl₀']
        simpa using hxx hp

theorem xs_bound {ls : List Nat} (hl : ls.length = b.uvars) {ps : List V}
    (hps : Ext M ls b.params [] ps) (h0 : lev ls b ≠ 0)
    {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors)
    {a : Nat} (ha : a < c.fields.length) {xs : List VExpr} {k : Nat} {idx : List VExpr}
    (hcert : (c.fields[a]!).cert = .recursive xs k idx) {fs : List V} (hfs : fs.length = a)
    (hfit : FFit M ls (unitTuple M ls b ps.reverse) (c.fields.take a) ps.reverse fs) :
    BoundS (lev ls b) (telOf M ls xs (fs.reverse ++ ps.reverse)) := by
  have hU := patch_tupleFn (M := M) (b := b) (ls₀ := ls) (ρ₀ := ps.reverse)
    (unitTuple_space (w := lev ls b))
  have hsat := (S.ffit_iff_sat hU hl hj hc hps a (Nat.le_of_lt ha) fs hfs).mp
    (by rw [patch_at]; exact hfit)
  have hfok := S.field_full hj hc ha
  have hM₁ := (S.model₁ hU).1
  have hctx := S.fctx_consts hj hc a (Nat.le_of_lt ha)
  unfold Setting.FieldFull at hfok
  simp only [hcert] at hfok
  obtain ⟨_, _, ⟨_, hd⟩, hxs, _, _, _, hsort⟩ := hfok
  have hcR := (constsIn_forallTel xs _).mp (IsDefEq.constsIn S.good₁.2 hd hctx).2.1
  have hxfree : ∀ A ∈ xs, ConstsIn (fun c => M₁ M b (patch M b ls ps.reverse
      (unitTuple M ls b ps.reverse)) c = M c) A :=
    fun A hA => S.free (hcR.1 A hA) (hxs A hA)
  refine boundS_telOf fun e he ys hys => ?_
  obtain ⟨u, hu, hle⟩ := hsort e he
  have hys₁ := (Ext.congrM (fun _ h => h) (fun A hA => (hxfree A (List.mem_of_mem_take hA)).mono
    fun _ h => h.symm)).mp hys
  have hsat' := Sat.of_ext hsat hys₁
  have hmem := (hM₁.sound hu ls _ hsat').2
  have eget : xs[e]! = xs[e] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem he]; rfl
  rw [eget, interp_congr (hxfree _ (List.getElem_mem he))] at hmem
  simp only [interp] at hmem
  exact univ_mono (hle ls h0) _ hmem

theorem piece_mem {ls : List Nat} (hl : ls.length = b.uvars) {ps : List V}
    (hps : Ext M ls b.params [] ps) (h0 : lev ls b ≠ 0) (m q a : Nat) :
    piece M ls b ps.reverse m q a ∈ˢ (univ (lev ls b) : V) := by
  have hU := univ_isTGUniverse (V := V) h0
  unfold piece
  split
  · rename_i hm
    split
    · rename_i c hcq
      have hc : c ∈ (b.types[m]!).ctors := List.mem_of_getElem? hcq
      split
      · rename_i f hfa
        obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.mp hfa
        split
        · rename_i xs k idx hcert
          refine hU.famUnion_mem (towerSet_mem_univ _
            (S.bound_take hl hps h0 unitTuple_space hm hc (Nat.le_of_lt ha))) fun t ht => ?_
          obtain ⟨fs, hfit, rfl⟩ := (mem_towerSet_pos h0).mp ht
          have hfit' := fitsS_telF.mp hfit
          have hlen : fs.length = a := by
            rw [hfit'.length_eq]; simp; omega
          rw [projList_mkTower a fs hlen]
          exact extSet_mem_univ h0 (S.xs_bound hl hps h0 hm hc ha
            (by rw [BlockModel.Setting.getElem!_fields ha]; exact hcert) hlen hfit')
        · exact empty_mem_univ _
      · exact empty_mem_univ _
    · exact empty_mem_univ _
  · exact empty_mem_univ _

theorem hBound {ls : List Nat} (hl : ls.length = b.uvars) {ps : List V}
    (hps : Ext M ls b.params [] ps) : HBound M ls b ps.reverse := by
  intro h0
  refine ⟨natUnion fun m => natUnion fun q => natUnion fun a => piece M ls b ps.reverse m q a,
    natUnion_mem_univ_pos h0 fun m => natUnion_mem_univ_pos h0 fun q =>
      natUnion_mem_univ_pos h0 fun a => S.piece_mem hl hps h0 m q a, ?_⟩
  intro X hX m hm q c hcq fs hfit a f xs k idx hfa hcert t ht
  have hc : c ∈ (b.types[m]!).ctors := List.mem_of_getElem? hcq
  obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.mp hfa
  have hcert' : (c.fields[a]!).cert = .recursive xs k idx := by
    rw [BlockModel.Setting.getElem!_fields ha]; exact hcert
  have hflen := hfit.length_eq
  have hta : (fs.take a).length = a := by simp; omega
  have hfit₀ : FFit M ls X (c.fields.take a) ps.reverse (fs.take a) := by
    have e1 : c.fields = c.fields.take a ++ c.fields.drop a := (List.take_append_drop a _).symm
    have e2 : fs = fs.take a ++ fs.drop a := (List.take_append_drop a _).symm
    rw [e1, e2] at hfit
    exact ((FFit.append (by simp; omega)).mp hfit).1
  obtain ⟨fs', hl', hfit', hag⟩ := S.erase_fit hl hps hm hc a (Nat.le_of_lt ha) _ hta hfit₀
  have hri := (S.ctorSyn hm hc).recIndep
  have e : extSet M ls xs (pre ps.reverse fs a) = extSet M ls xs (fs'.reverse ++ ps.reverse) :=
    extSet_congr fun e he ys hys =>
      interp_agree_fields (M := M) (ls := ls) (c := c) hta hl' hag xs[e]
        (fun i hi ⟨xs₀, k₀, idx₀, hr⟩ => by
          have := (recIndep_spec hri (by omega) ha hi hr).2 xs k idx hcert' e he
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem he] at this
          exact this) ys hys
  rw [e] at ht
  refine mem_natUnion.mpr ⟨m, mem_natUnion.mpr ⟨q, mem_natUnion.mpr ⟨a, ?_⟩⟩⟩
  unfold piece
  simp only [hm, ite_true, hcq, List.getElem?_eq_getElem ha, hcert]
  refine mem_sUnion.mpr ⟨_, SetTheory.mem_image.mpr ⟨mkTower fs',
    (mem_towerSet_pos h0).mpr ⟨fs', fitsS_telF.mpr hfit', rfl⟩, rfl⟩, ?_⟩
  rw [projList_mkTower a fs' hl']; exact ht

end Setting
end Soulgem.BlockModel
