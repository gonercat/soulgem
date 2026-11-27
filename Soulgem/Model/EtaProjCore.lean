import Soulgem.Model.NestedElim
import Soulgem.Model.BlockEta
import Soulgem.CoreModel
import Soulgem.Spec.Env
import Soulgem.Model.NestedModel

/-! # Structure eta through projection functions: the model lemmas -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u

variable {V : Type u} [SetTheory V]

theorem le_foldl_addDefEq : ∀ (dfs : List VDefEq) (e : VEnv), e ≤ dfs.foldl VEnv.addDefEq e
  | [], _ => .rfl
  | x :: xs, e => VEnv.LE.trans (show e ≤ e.addDefEq x from ⟨fun h => h, fun h => Or.inr h⟩)
      (le_foldl_addDefEq xs (e.addDefEq x))

theorem le_iotaFold (b : SBlock) (e : VEnv) : e ≤ iotaFold b e := by
  rw [iotaFold_eq]; exact le_foldl_addDefEq _ _

section Tel
variable {M : CInterp V} {ls : List Nat}

theorem foldl_app_pt : ∀ xs : List V, xs.foldl app (pt : V) = pt
  | [] => rfl
  | x :: xs => by simp only [List.foldl, app_pt]; exact foldl_app_pt xs

theorem apps_mem_forallTel {R : VExpr} : ∀ {As : List VExpr} {ρ xs : List V} {f : V},
    f ∈ˢ interp M ls (Spec.forallTel As R) ρ → Ext M ls As ρ xs → xs.foldl app f ∈ˢ
        interp M ls R (xs.reverse ++ ρ)
  | [], _, _, _, hf, .nil => hf
  | _ :: _, _, _ :: _, _, hf, .cons hx hxs => by
    simpa [List.foldl, List.reverse_cons, List.append_assoc] using apps_mem_forallTel
        (app_mem_cpi hf hx) hxs

theorem eq_pt_of_mem_forallTel {R : VExpr} : ∀ {As : List VExpr} {ρ : List V} {f : V},
    (∀ xs, Ext M ls As ρ xs → ∀ y, y ∈ˢ interp M ls R (xs.reverse ++ ρ) → y = pt) →
    f ∈ˢ interp M ls (Spec.forallTel As R) ρ → f = pt
  | [], _, f, h, hf => h [] .nil f hf
  | A :: As, ρ, f, h, hf => by
    obtain ⟨g, -, rfl⟩ := mem_cpi.mp hf
    have hv : ∀ a, a ∈ˢ interp M ls A ρ → app g a = pt := fun a ha => by
      rw [← app_collapse ha]
      exact eq_pt_of_mem_forallTel (fun xs hxs y hy => h (a :: xs) (.cons ha hxs) y
        (by simpa [List.reverse_cons, List.append_assoc] using hy)) (app_mem_cpi hf ha)
    simp only [collapse, ite_eq_left hv]

end Tel

def RecTypes (env : VEnv) (rec : List RBlock) : Prop :=
  (∀ r ∈ rec, ∀ t ∈ r.b.types.take r.nuser, env.constants t.name = some ⟨r.b.uvars, t.type⟩) ∧
    rec.Pairwise fun r r' => ∀ t ∈ r.b.types.take r.nuser, ∀ t' ∈ r'.b.types.take r'.nuser,
        t.name ≠ t'.name

theorem RecTypes.snoc {env e₁ env' : VEnv} {rec : List RBlock} {r₀ : RBlock} (ih : RecTypes env rec)
    (h1 : addFold env (nTypeConsts r₀.b r₀.nuser) = some e₁) (hle : e₁ ≤ env') :
        RecTypes env' (rec ++ [r₀]) := by
  have hfr := (addFold_spec h1).1
  refine ⟨fun r hr t ht => ?_, List.pairwise_append.mpr ⟨ih.2, List.pairwise_singleton _ _, ?_⟩⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact ((addFold_spec h1).2.2.1.trans hle).constants (ih.1 r hr t ht)
    · rw [List.mem_singleton.mp hr] at ht ⊢
      exact hle.constants (addFold_get h1 (List.mem_map.mpr ⟨t, ht, rfl⟩))
  · intro r hr r' hr' t ht t' ht' hn
    rw [List.mem_singleton.mp hr'] at ht'
    have := hfr _ (List.mem_map.mpr ⟨t', ht', rfl⟩)
    rw [← hn, ih.1 r hr t ht] at this; cases this

theorem admits_recTypes {base env : VEnv} {rec : List RBlock} (H : Admits base env rec) :
    RecTypes env rec := by
  induction H with
  | base => exact ⟨nofun, .nil⟩
  | «def» _ _ hadd ih =>
    exact ⟨fun r hr t ht => (VEnv.LE.trans (VEnv.addConst_le hadd) VEnv.addDefEq_le).constants
        (ih.1 r hr t ht), ih.2⟩
  | «opaque» _ _ hadd ih => exact ⟨fun r hr t ht => (VEnv.addConst_le hadd).constants
      (ih.1 r hr t ht), ih.2⟩
  | etaProj _ _ _ _ _ _ ih => exact ⟨fun r hr t ht => VEnv.addDefEq_le.constants
      (ih.1 r hr t ht), ih.2⟩
  | @plain env env' rec b _ _ hadd ih =>
    obtain ⟨e₁, e₂, e₃, h1, h2, h3, rfl⟩ := add_spec hadd
    rw [withTypes_eq] at h1
    exact ih.snoc (r₀ := RBlock.plain b) (by
        simpa [nTypeConsts, typeConsts, RBlock.plain, SBlock.ntypes] using h1)
      (((addFold_spec h2).2.2.1.trans (addFold_spec h3).2.2.1).trans
          ((le_iotaFold b e₃).trans (addEta_le b _)))
  | @nested env env' rec u b tr fams _ _ _ hadd ih =>
    obtain ⟨e₁, e₂, e₃, h1, h2, h3, rfl⟩ := addNested_spec hadd
    exact ih.snoc h1 (((addFold_spec h2).2.2.1.trans (addFold_spec h3).2.2.1).trans
      ((le_foldl_addDefEq _ _).trans (le_foldl_addDefEq _ _)))

theorem plain_type_const {base env : VEnv} {rec : List RBlock} (H : Admits base env rec)
    {b : SBlock}
    (hb : RBlock.plain b ∈ rec) {t : SType} (ht : t ∈ b.types) : env.constants t.name =
        some ⟨b.uvars, t.type⟩ :=
  (admits_recTypes H).1 _ hb t (by simpa [RBlock.plain, SBlock.ntypes] using ht)

theorem interp_ownApp {M : CInterp V} {ls : List Nat} {b : SBlock}
    (hl : ls.length = b.uvars) (n : Name)
    {qs zs : List V} (hq : qs.length = b.nparams) (es : List VExpr) :
    interp M ls (appN (.const n (ownLevels b.uvars)) (vars (b.nparams + zs.length) 0
        b.nparams ++ es))
      (qs ++ zs).reverse = (qs ++ es.map (interp M ls · (qs ++ zs).reverse)).foldl app
          (M n ls) := by
  rw [interp_appN, List.map_append, interp_param_vars M ls (by omega)
    (by simp only [List.length_reverse, List.length_append, hq])]
  simp [interp, ownLevels_eval hl, ← hq]

theorem interp_sApp {M : CInterp V} {ls : List Nat} {b : SBlock}
    (hl : ls.length = b.uvars) (n : Name) {qs : List V} (hq : qs.length = b.nparams) :
    interp M ls (appN (.const n (ownLevels b.uvars)) (vars b.nparams 0 b.nparams)) qs.reverse =
        qs.foldl app (M n ls) := by
  simpa using interp_ownApp (M := M) hl n (zs := []) hq []

noncomputable def projVals (M : CInterp V) (ls : List Nat) (nm : List Name) (qs : List V)
    (x : V) : List V :=
  (List.range nm.length).map fun j => (qs ++ [x]).foldl app (M (nm.getD j .anonymous) ls)

theorem projVals_getD {M : CInterp V} {ls : List Nat} {nm : List Name} {qs : List V}
    {x : V} {j : Nat} (hj : j < nm.length) :
    (projVals M ls nm qs x).getD j pt = (qs ++ [x]).foldl app (M (nm.getD j .anonymous) ls) := by
  simp [projVals, List.getD_eq_getElem?_getD, hj]

theorem interp_fieldTyP {M : CInterp V} {ls : List Nat} {b : SBlock} {c : SCtor} {nm : List Name}
    {qs zs : List V}
    {x : V} {j D : Nat} (hl : ls.length = b.uvars) (hql : qs.length = b.nparams)
        (hD : b.nparams + zs.length = D)
    (hjf : j < c.fields.length)
    (hcl : (c.fields[j]!).ty.ClosedN (b.nparams + j)) (hyl : (projVals M ls nm qs x).length =
        c.fields.length) :
    interp M ls (b.fieldTyP (nm.getD · .anonymous) c (D + 1) D j) (x :: (qs ++ zs).reverse) =
      interp M ls (c.fields[j]!).ty (((projVals M ls nm qs x).take j).reverse ++ qs.reverse) := by
  subst hD
  unfold SBlock.fieldTyP
  split
  · next hnd =>
    have := interp_place_nodep (M' := M) (ls' := ls) (b := b) (c := c) (i := j)
        (by simpa using hnd) hcl
      (ps := qs) (zs := zs) hql (d := b.nparams + zs.length) rfl x ((projVals M ls nm qs x).take j)
          (by simp [hyl]; omega)
    simpa using this
  · have := interp_subst M ls (fun j' => if j' < j then b.projApp (nm.getD · .anonymous)
      (b.nparams + zs.length + 1)
        (b.nparams + zs.length) (j - 1 - j') else var (b.nparams + zs.length + 1)
            (b.nparams - 1 - (j' - j)))
        (c.fields[j]!).ty 0 (b.nparams + j) [] (x :: (qs ++ zs).reverse)
      (((projVals M ls nm qs x).take j).reverse ++ qs.reverse) (by simpa using hcl) rfl ?_
    · simpa using this
    intro i hi
    split
    · next hij =>
      rw [getD_append_lt (by simp [hyl]; omega), getD_reverse (by simp [hyl]; omega),
        List.length_take, Nat.min_eq_left (by simp [hyl]; omega),
        show (List.take j (projVals M ls nm qs x)).getD (j - 1 - i) pt =
            (projVals M ls nm qs x).getD (j - 1 - i) pt by
          simp [List.getD_eq_getElem?_getD, show j - 1 - i < j by omega],
        projVals_getD (by simp [projVals] at hyl; omega)]
      have := interp_ownApp (M := M) hl (nm.getD (j - 1 - i) .anonymous) (zs := zs ++ [x]) hql
        [var (b.nparams + zs.length + 1) (b.nparams + zs.length)]
      have hv : interp M ls (var (b.nparams + zs.length + 1) (b.nparams + zs.length))
          (x :: zs.reverse ++ qs.reverse) = x := by
        have := interp_var (M := M) (ls := ls) (xs := qs ++ zs ++ [x])
            (d := b.nparams + zs.length + 1)
          (L := b.nparams + zs.length) (by simp [hql]; omega) (by omega)
        simpa [List.getD_eq_getElem?_getD, hql] using this
      simp only [List.length_append, List.length_singleton, ← Nat.add_assoc, ← List.append_assoc,
        List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons,
            List.map_nil] at this
      rw [hv] at this
      simpa [SBlock.projApp] using this.symm
    · next hij =>
      have hv := interp_var (M := M) (ls := ls) (xs := qs ++ zs ++ [x])
          (d := b.nparams + zs.length + 1)
        (L := b.nparams - 1 - (i - j)) (by simp [hql]; omega) (by omega)
      rw [show (qs ++ zs ++ [x]).getD (b.nparams - 1 - (i - j)) pt =
          qs.getD (b.nparams - 1 - (i - j)) pt by
        simp [List.getD_eq_getElem?_getD, List.append_assoc,
          List.getElem?_append_left (show b.nparams - 1 - (i - j) < qs.length by omega)]] at hv
      rw [show (qs ++ zs ++ [x]).reverse = x :: (qs ++ zs).reverse by simp] at hv
      rw [hv, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hyl]; omega)]
      simp only [List.length_reverse, List.length_take,
        Nat.min_eq_left (show j ≤ (projVals M ls nm qs x).length by simp [hyl]; omega)]
      rw [← List.getD_eq_getElem?_getD, getD_reverse (by omega), hql]

theorem constsIn_of_not_mentions {P Q : Name → Prop} {ns : List Name}
    (hPQ : ∀ c, P c → c ∉ ns → Q c) :
    ∀ {e : VExpr}, mentions ns e = false → ConstsIn P e → ConstsIn Q e
  | .bvar _, _, _ | .sort _, _, _ => trivial
  | .const c _, hm, h => hPQ c h (by simpa [mentions] using hm)
  | .app _ _, hm, h | .lam _ _, hm, h | .forallE _ _, hm, h => by
    simp only [mentions, Bool.or_eq_false_iff] at hm
    exact ⟨constsIn_of_not_mentions hPQ hm.1 h.1, constsIn_of_not_mentions hPQ hm.2 h.2⟩

theorem setting_le {base env envJ envJ₁ : VEnv} {rec : List RBlock} (H : Admits base env rec)
    {b : SBlock}
    (hb : RBlock.plain b ∈ rec) (hle : envJ ≤ env) (hwt : b.withTypes envJ = some envJ₁) :
        envJ₁ ≤ env := by
  rw [withTypes_eq] at hwt
  obtain ⟨-, hdf, -, hcs, -, -⟩ := addFold_spec hwt
  refine ⟨fun h => ?_, fun h => hle.defeqs (hdf ▸ h)⟩
  rcases hcs _ _ h with ⟨y, hy, rfl, rfl⟩ | h'
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy; exact plain_type_const H hb ht
  · exact hle.constants h'

theorem ext_delta {M : CInterp V} {ls : List Nat} {b : SBlock} {t : SType} {qs : List V} {x : V}
    (hl : ls.length = b.uvars) (ht : b.types = [t]) (hq : Ext M ls b.params [] qs)
    (hx : x ∈ˢ qs.foldl app (M t.name ls)) :
    Ext M ls (b.params ++ [appN (.const (b.types[0]!).name (ownLevels b.uvars))
        (vars b.nparams 0 b.nparams)])
      [] (qs ++ [x]) := by
  refine Ext.append hq (.cons ?_ .nil)
  rw [List.append_nil, interp_sApp hl _ (Ext.length_eq M ls hq)]; simpa [ht] using hx

theorem interp_lastVar {M : CInterp V} {ls : List Nat} {n : Nat} {qs : List V} {x : V}
    (hql : qs.length = n) : interp M ls (var (n + 1) n) (x :: qs.reverse) = x := by
  have := interp_var (M := M) (ls := ls) (xs := qs ++ [x]) (d := n + 1) (L := n)
      (by simp [hql]) (by omega)
  simpa [List.getD_eq_getElem?_getD, hql] using this

theorem ext_delta_inv {M : CInterp V} {ls : List Nat} {b : SBlock} {t : SType} {ws : List V}
    (hl : ls.length = b.uvars) (ht : b.types = [t])
    (hws : Ext M ls (b.params ++ [appN (.const (b.types[0]!).name (ownLevels b.uvars))
        (vars b.nparams 0 b.nparams)])
      [] ws) : ∃ qs x, ws = qs ++ [x] ∧ Ext M ls b.params [] qs ∧ x ∈ˢ
          qs.foldl app (M t.name ls) := by
  obtain ⟨hq, hz'⟩ := Ext.split hws
  obtain ⟨x, xs, hd, hx, hn⟩ := Ext_cons_iff.mp hz'
  obtain rfl := Ext_nil_iff.mp hn
  refine ⟨_, x, by rw [← hd, List.take_append_drop], hq, ?_⟩
  rw [List.append_nil, interp_sApp hl _ (Ext.length_eq M ls hq)] at hx; simpa [ht] using hx

structure ProjRec (env : VEnv) (b : SBlock) (t : SType) (c : SCtor) (nm : List Name) : Prop where
  ht : b.types = [t]
  hc : t.ctors = [c]
  hlen : nm.length = c.fields.length
  hk : ∀ i < nm.length, env.constants (nm.getD i .anonymous) =
      some ⟨b.uvars, b.projTyP (nm.getD · .anonymous) c i⟩
  hδ : ∀ i < nm.length, (c.fields[i]!).sort.isAlwaysZero = false →
    env.defeqs (b.projDefVal (nm.getD i .anonymous) (nm.getD · .anonymous) c i).toDefEq

section Proj
variable {M MJ : CInterp V} {env envJ envJ₁ : VEnv} {b : SBlock} {t : SType} {c : SCtor}
    {nm : List Name}
  {ls : List Nat} {qs : List V} {x : V}

theorem field_closed (S : Setting MJ envJ envJ₁ b) (ht : b.types = [t])
    (hc : t.ctors = [c]) {j : Nat}
    (hj : j < c.fields.length) : (c.fields[j]!).ty.ClosedN (b.nparams + j) :=
  (S.field_scoped (P := fun _ => True) (fun _ _ => trivial) (by simp [SBlock.ntypes, ht])
    (show c ∈ (b.types[0]!).ctors by simp [ht, hc]) hj).1

theorem projVals_ext (hM : IsModel M env) (S : Setting MJ envJ envJ₁ b) (R : ProjRec env b t c nm)
    (hl : ls.length = b.uvars) (hq : Ext M ls b.params [] qs) (hx : x ∈ˢ
        qs.foldl app (M t.name ls)) :
    Ext M ls (c.fields.map (·.ty)) qs.reverse (projVals M ls nm qs x) := by
  obtain ⟨ht, hc, hlen, hk, -⟩ := R
  have hql : qs.length = b.nparams := Ext.length_eq M ls hq
  have hyl : (projVals M ls nm qs x).length = c.fields.length := by simp [projVals, hlen]
  have hΔ := ext_delta hl ht hq hx
  refine Ext.of_get (by simpa using hyl) fun j hj _ => ?_
  have hjn : j < nm.length := by simpa [hlen] using hj
  have hjf : j < c.fields.length := by simpa using hj
  have hmem := apps_mem_forallTel (hM.const (hk j hjn) ls hl []) hΔ
  simp only [List.getElem_map]
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.append_nil] at hmem
  have e := interp_fieldTyP (M := M) (x := x) (nm := nm) (zs := []) (D := b.nparams) hl hql rfl hjf
    (field_closed S ht hc hjf) hyl
  rw [List.append_nil] at e
  have hfj : (c.fields[j]!) = c.fields[j] := by simp [hjf]
  rw [hfj] at e; rw [← e]; simpa [projVals] using hmem

theorem ext_field (hM : IsModel M env) (S : Setting MJ envJ envJ₁ b) (hle₁ : envJ₁ ≤ env)
    (ht : b.types = [t]) (hc : t.ctors = [c]) (hq : Ext M ls b.params [] qs) {gs : List V}
    (hE : Ext M ls (c.fields.map (·.ty)) qs.reverse gs) {i : Nat} (hi : i < c.fields.length) :
    gs.getD i pt ∈ˢ interp M ls (c.fields[i]!).ty ((gs.take i).reverse ++ qs.reverse) ∧
      interp M ls (c.fields[i]!).ty ((gs.take i).reverse ++ qs.reverse) ∈ˢ
          univ ((c.fields[i]!).sort.eval ls) := by
  have hd0 : 0 < b.ntypes := by simp [SBlock.ntypes, ht]
  have hc' : c ∈ (b.types[0]!).ctors := by simp [ht, hc]
  have hgl : gs.length = c.fields.length := by rw [Ext.length_eq _ _ hE]; simp
  have hfi : c.fields[i]! = c.fields[i] := by simp [hi]
  have hg := hE.get i (by simpa using hi) (by omega)
  simp only [List.getElem_map] at hg
  refine ⟨by simpa [hfi, List.getD_eq_getElem?_getD, hgl ▸ hi] using hg, ?_⟩
  rw [← List.take_append_drop i c.fields, List.map_append] at hE
  have hEi := (Ext.split hE).1
  simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at hEi
  have hsat : Sat M ls (Setting.fctx b c i) ((gs.take i).reverse ++ qs.reverse) := by
    have := Sat.of_ext (M := M) (ls := ls) (Γ := []) (ρ := []) trivial
        (Ext.append hq (by simpa using hEi))
    simpa [Setting.fctx] using this
  have hs := (hM.sound (VEnv.HasType.mono hle₁ (S.field_ok hd0 hc' hi).1) ls _ hsat).2
  simpa only [interp] using hs

theorem projFn_proof_pt (hM : IsModel M env) (S : Setting MJ envJ envJ₁ b) (hle₁ : envJ₁ ≤ env)
    (R : ProjRec env b t c nm) (hl : ls.length = b.uvars) {i : Nat} (hi : i < nm.length)
    (hz : (c.fields[i]!).sort.isAlwaysZero = true) : M (nm.getD i .anonymous) ls = pt := by
  have R' := R
  obtain ⟨ht, hc, hlen, hk, -⟩ := R
  have hif : i < c.fields.length := hlen ▸ hi
  refine eq_pt_of_mem_forallTel (fun ws hws y hy => ?_) (hM.const (hk i hi) ls hl [])
  obtain ⟨qs, x, rfl, hq, hx⟩ := ext_delta_inv hl ht hws
  have hE := projVals_ext hM S R' hl hq hx
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.append_nil] at hy
  have e := interp_fieldTyP (M := M) (nm := nm) (x := x) (zs := []) (D := b.nparams) hl
      (Ext.length_eq M ls hq) rfl hif
    (field_closed S ht hc hif) (by simp [projVals, hlen])
  rw [List.append_nil] at e; rw [e] at hy
  have hs := (ext_field hM S hle₁ ht hc hq hE hif).2
  rw [VLevel.eval_of_isAlwaysZero hz] at hs
  exact mem_univ_zero hs hy

theorem fields_consts (S : Setting MJ envJ envJ₁ b) (ht : b.types = [t]) (hc : t.ctors = [c])
    (hη : b.etaCtor? = some c) : ∀ A ∈ c.fields.map (·.ty), ConstsIn (Dom envJ) A := fun A hA => by
  have hd0 : 0 < b.ntypes := by simp [SBlock.ntypes, ht]
  have hc' : c ∈ (b.types[0]!).ctors := by simp [ht, hc]
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hA
  obtain ⟨-, -, -, -, -, hpl, -⟩ := etaCtor_spec hη
  exact constsIn_of_not_mentions (fun k h hn => S.dom_of_dom₁ h hn) (hpl f hf).2
    (S.fctx_consts hd0 hc' c.fields.length (Nat.le_refl _) f.ty
      (by
          simp only [Setting.fctx, List.take_length, List.mem_reverse, List.mem_append,
              List.mem_map]; exact .inr ⟨f, hf, rfl⟩))

theorem slotCtor_struct (hC : CanonR M env (RBlock.plain b) MJ envJ envJ₁) (ht : b.types = [t])
    (hc : t.ctors = [c]) : Dom env c.name ∧ ∀ ls ρ, ls.length = b.uvars → Ext MJ ls b.params [] ρ →
      interp M ls (appN (.const c.name (ownLevels b.uvars)) (vars b.nparams 0
          b.nparams)) ρ.reverse =
        ρ.foldl app (Setting.ctorVal b (Setting.Mc MJ b) ls 0 c) := by
  have := hC.slotCtors 0 (by simp [RBlock.plain, SBlock.ntypes, ht]) 0 c
    (by simp [RBlock.plain, ctorsOf, ht, hc]) _ (by
        simp [RBlock.slotKey, RBlock.plain, SBlock.ntypes, ht]) t.name
    (ownLevels b.uvars) (vars b.nparams 0 b.nparams) (headArgs_appN_const _ _ _)
  simpa only [RBlock.plain, ht, List.getElem!_cons_zero, replacePrefix_same] using this

theorem etaRhs_val (hM : IsModel M env) (hC : CanonR M env (RBlock.plain b) MJ envJ envJ₁)
    (R : ProjRec env b t c nm)
    (hη : b.etaCtor? = some c) (hl : ls.length = b.uvars) (hq : Ext M ls b.params [] qs)
    (hx : x ∈ˢ qs.foldl app (M t.name ls)) :
    interp M ls (appN (.const c.name (ownLevels b.uvars)) (vars (b.nparams + 1) 0 b.nparams ++
      (List.range c.fields.length).map (b.projApp (nm.getD · .anonymous) (b.nparams + 1)
          b.nparams))) (x :: qs.reverse) =
      enc ls b 0 (projVals M ls nm qs x) := by
  have R' := R
  obtain ⟨ht, hc, hlen, hk, -⟩ := R
  have S : Setting MJ envJ envJ₁ b := hC.setting
  have hql : qs.length = b.nparams := Ext.length_eq M ls hq
  have hE := projVals_ext hM S R' hl hq hx
  have hyl : (projVals M ls nm qs x).length = c.fields.length := by simp [projVals, hlen]
  have hv := interp_lastVar (M := M) (ls := ls) (n := b.nparams) (x := x) hql
  have happ : ∀ j, interp M ls (b.projApp (nm.getD · .anonymous) (b.nparams + 1) b.nparams j)
      (x :: qs.reverse) =
      (qs ++ [x]).foldl app (M (nm.getD j .anonymous) ls) := fun j => by
    have := interp_ownApp (M := M) hl (nm.getD j .anonymous) (zs := [x]) hql
        [var (b.nparams + 1) b.nparams]
    simpa [SBlock.projApp, hv] using this
  have hmk := interp_ownApp (M := M) hl c.name (zs := [x]) hql
    ((List.range c.fields.length).map (b.projApp (nm.getD · .anonymous) (b.nparams + 1) b.nparams))
  simp only [List.length_singleton, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_map,
    Function.comp_def, happ] at hmk
  have hys : (List.range c.fields.length).map (fun j => (qs ++ [x]).foldl app
      (M (nm.getD j .anonymous) ls)) =
      projVals M ls nm qs x := by simp [projVals, hlen]
  rw [hmk, hys]
  have hag : ∀ k, Dom envJ k → M k = Setting.Mc MJ b k := fun k h =>
      (hC.agree k h).trans (S.agree h).symm
  have hqc := (Ext.congrM hag S.params_consts').mp hq
  have hyc := (Ext.congrM hag (fields_consts S ht hc hη)).mp hE
  have e2 := (slotCtor_struct hC ht hc).2 ls qs hl ((Ext.congrM (fun k h => hC.agree k h)
      S.params_consts').mp hq)
  have hown := interp_ownApp (M := M) hl c.name (zs := []) hql []
  simp only [List.length_nil, Nat.add_zero, List.append_nil, List.map_nil] at hown
  rw [hown] at e2
  rw [List.foldl_append, e2]
  simp only [Setting.ctorVal]
  rw [apps_lamTel hqc, List.append_nil, apps_lamTel hyc, List.take_left' (by simp [hyl]),
      List.reverse_reverse]

theorem projVals_enc₀ (hM : IsModel M env) (hC : CanonR M env (RBlock.plain b) MJ envJ envJ₁)
    (hle₁ : envJ₁ ≤ env) (R : ProjRec env b t c nm) (hη : b.etaCtor? = some c)
    (hl : ls.length = b.uvars) (hq : Ext M ls b.params [] qs) (hx : x ∈ˢ
        qs.foldl app (M t.name ls)) :
    x = enc ls b 0 (projVals M ls nm qs x) := by
  have R' := R
  obtain ⟨ht, hc, hlen, hk, hδ⟩ := R
  have S : Setting MJ envJ envJ₁ b := hC.setting
  obtain ⟨hnt, -, hcs, hidx, -, -, hlg⟩ := etaCtor_facts hη
  have hd0 : 0 < b.ntypes := by omega
  have hcq : (ctorsOf b 0)[0]? = some c := by rw [hcs]; rfl
  have hql : qs.length = b.nparams := Ext.length_eq M ls hq
  obtain ⟨e₂, e₃, h2, h3, -, hrec⟩ := hC.recs rfl hd0
  have hag : ∀ k, Dom envJ k → M k = M₃ MJ b k := fun k h =>
    (hC.agree k h).trans ((S.agree h).symm.trans (BlockModel.Setting.hag₃₁ h2 h3 k
        (Dom.mono S.le₁ h)).symm)
  have hfc := fields_consts S ht hc hη
  have hqJ : Ext MJ ls b.params [] qs := (Ext.congrM (fun k h => hC.agree k h)
      S.params_consts').mp hq
  have hSv : qs.foldl app (M t.name ls) = app (carrier MJ ls b qs.reverse 0) (mkTower []) := by
    obtain ⟨k, hk', -, -, -, hread⟩ := hC.slots 0 (by simpa [RBlock.plain] using hd0)
    simp only [RBlock.slotKey, RBlock.plain, ht, ite_eq_left hd0, List.getElem?_cons_zero,
        Option.map_some,
      Option.some.injEq] at hk'
    subst hk'
    have := hread ls qs hl hqJ
    rw [interp_sApp hl _ hql] at this
    rw [this, ← S.type_apps h2 h3 hη hqJ, BlockModel.Setting.hag₃₁ (M := MJ) (b := b) h2 h3 _
        (S.type_dom hd0)]
    rfl
  have hencS : ∀ gs, FFit MJ ls (carrier MJ ls b qs.reverse) c.fields qs.reverse gs →
      enc ls b 0 gs ∈ˢ app (carrier MJ ls b qs.reverse 0) (mkTower []) := fun gs hg => by
    have hi : cidx MJ ls qs.reverse c gs ∈ˢ Is MJ ls b qs.reverse 0 :=
      mkTower_mem_extSet MJ _ (S.ctor_result hl hcq hqJ hg)
    have hcidx : cidx MJ ls qs.reverse c gs = mkTower [] := by
      have := Ext.length_eq MJ _ (S.ctor_result hl hcq hqJ hg)
      rw [hidx] at this; simp [cidx, List.eq_nil_of_length_eq_zero (by simpa using this)]
    simpa [hcidx] using enc_mem S.hK (S.hSmall hl hqJ) (S.hBound hl hqJ) hd0 hcq hg hi
  have hext : ∀ gs, FFit MJ ls (carrier MJ ls b qs.reverse) c.fields qs.reverse gs →
      Ext M ls (c.fields.map (·.ty)) qs.reverse gs := fun gs hg =>
    (Ext.congrM hag hfc).mpr (S.ffit_ext h2 h3 hη hl hqJ hg)
  have hq0 : ∀ {q c'}, (ctorsOf b 0)[q]? = some c' → q = 0 ∧ c' = c := fun {q c'} h => by
    rw [hcs] at h; cases q <;> simp at h; exact ⟨rfl, h.symm⟩
  have hi0 : (mkTower [] : V) ∈ˢ Is MJ ls b qs.reverse 0 := mkTower_mem_extSet MJ _
      (by rw [hidx]; exact .nil)
  have key : ∀ i, i < c.fields.length → ∀ gs, FFit MJ ls (carrier MJ ls b qs.reverse) c.fields
      qs.reverse gs →
      (qs ++ [enc ls b 0 gs]).foldl app (M (nm.getD i .anonymous) ls) = gs.getD i pt := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i IH =>
    intro hi gs hg
    have hgE := hext gs hg
    have hin : i < nm.length := hlen ▸ hi
    cases hz : (c.fields[i]!).sort.isAlwaysZero with
    | true =>
      have hf := ext_field hM S hle₁ ht hc hq hgE hi
      rw [projFn_proof_pt hM S hle₁ R' hl hin hz, foldl_app_pt]
      have h0 := hf.2; rw [VLevel.eval_of_isAlwaysZero hz] at h0
      exact (mem_univ_zero h0 hf.1).symm
    | false =>
      have hlv : ls.length = (b.projDefVal (nm.getD i .anonymous) (nm.getD · .anonymous) c
          i).toDefEq.uvars := by
        simpa [SBlock.projDefVal, VDefVal.toDefEq] using hl
      have hdf := (hM.defeq (hδ i hin hz) ls hlv []).1
      simp only [VDefVal.toDefEq, SBlock.projDefVal, interp] at hdf
      rw [map_eval_params hl] at hdf
      have hz' : enc ls b 0 gs ∈ˢ qs.foldl app (M t.name ls) := hSv ▸ hencS gs hg
      rw [hdf, SBlock.projValP, SBlock.projDefP]
      simp only []
      rw [interp_lamTel', apps_lamTel (ext_delta hl ht hq hz'), List.append_nil, interp_appN,
          List.map_append,
        interp_param_vars M ls (by omega) (by simp [hql]), ite_eq_left hlg]
      simp only [interp, List.map_cons, List.map_nil, ownLevels_eval hl]
      have hρ : (qs ++ [enc ls b 0 gs]).reverse.reverse.take b.nparams = qs := by simp [hql]
      have hv : interp M ls (var (b.nparams + 1) b.nparams) (qs ++ [enc ls b 0 gs]).reverse =
          enc ls b 0 gs := by
        simpa using interp_lastVar (M := M) (ls := ls) (n := b.nparams) (x := enc ls b 0 gs) hql
      have hmn : interp M ls (Spec.lamTel (b.etaFields c (b.nparams + 1))
          (var (b.nparams + 1 + c.fields.length) (b.nparams + 1 + i)))
              (qs ++ [enc ls b 0 gs]).reverse =
          Soulgem.lamTel (M₃ MJ b) ls (b.etaFields c (b.nparams + 1))
            (interp M ls (var (b.nparams + 1 + c.fields.length) (b.nparams + 1 + i)))
                (qs ++ [enc ls b 0 gs]).reverse := by
        rw [interp_lamTel']
        refine lamTel_congrM' hag fun A hA => ?_
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
        have ha' : a < c.fields.length := List.mem_range.mp ha
        exact constsIn_consumeAnn _ ((constsIn_place _ _ _ _).mpr
            (hfc _ (List.mem_map.mpr ⟨_, by simp [ha'], rfl⟩)))
      have hSapp : interp M ls (appN (.const (b.types[0]!).name (ownLevels b.uvars))
          (vars (b.nparams + 1) 0 b.nparams))
          (qs ++ [enc ls b 0 gs]).reverse = app (carrier MJ ls b qs.reverse 0) (mkTower []) := by
        have := interp_ownApp (M := M) hl (b.types[0]!).name (zs := [enc ls b 0 gs]) hql []
        simp only [List.length_singleton, List.append_nil, List.map_nil] at this
        rw [this, ← hSv]; simp [ht]
      have hcl := field_closed S ht hc hi
      have hF : ∀ gs', FFit MJ ls (carrier MJ ls b qs.reverse) c.fields qs.reverse gs' →
          interp M ls (b.fieldTyP (nm.getD · .anonymous) c (b.nparams + 1 + 1) (b.nparams + 1) i)
            (enc ls b 0 gs' :: (qs ++ [enc ls b 0 gs]).reverse) =
          interp M ls (c.fields[i]!).ty ((gs'.take i).reverse ++ qs.reverse) := fun gs' hg' => by
        have htk : (projVals M ls nm qs (enc ls b 0 gs')).take i = gs'.take i := by
          apply List.ext_getElem (by simp [projVals, hlen, FFit.length_eq (M := MJ) (ls := ls) hg'])
          intro j h1 h2
          have hj : j < i := by simp at h1; omega
          simp only [projVals, List.getElem_take, List.getElem_map, List.getElem_range]
          have hj' : j < gs'.length := by simp at h2; omega
          rw [IH j hj (by omega) gs' hg']; simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hj']
        rw [interp_fieldTyP (zs := [enc ls b 0 gs]) (D := b.nparams + 1) hl hql rfl hi hcl
            (by simp [projVals, hlen]), htk]
      rw [hρ, hv, hmn, hSapp]
      have hgd : ∀ ys : List V, ys.length = c.fields.length →
          interp M ls (var (b.nparams + 1 + c.fields.length) (b.nparams + 1 + i))
              (qs ++ [enc ls b 0 gs] ++ ys).reverse =
            ys.getD i pt := fun ys hys => by
        rw [interp_var (M := M) (ls := ls) (xs := qs ++ [enc ls b 0 gs] ++ ys)
            (by simp [hql, hys]; omega) (by omega),
          List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by simp [hql])]
        simp [hql]
      generalize hmot : clam (app (carrier MJ ls b qs.reverse 0) (mkTower [])) (fun x =>
        interp M ls (b.fieldTyP (nm.getD · .anonymous) c (b.nparams + 1 + 1) (b.nparams + 1) i)
          (x :: (qs ++ [enc ls b 0 gs]).reverse)) = mot
      have hmotS : mot ∈ˢ cpi (app (carrier MJ ls b qs.reverse 0) (mkTower [])) fun _ =>
          univ ((c.fields[i]!).sort.eval ls) := by
        rw [← hmot]
        refine clam_mem_cpi fun w hw => ?_
        obtain ⟨q, c', gs', hq', hg', -, rfl⟩ := S.mem_carrier_inv hl hqJ hd0 hi0 hw
        obtain ⟨rfl, rfl⟩ := hq0 hq'
        rw [hF gs' hg']; exact (ext_field hM S hle₁ ht hc hq (hext gs' hg') hi).2
      have hH : ∀ fs', FFit MJ ls (carrier MJ ls b qs.reverse) c.fields qs.reverse fs' →
          interp M ls (var (b.nparams + 1 + c.fields.length) (b.nparams + 1 + i))
              (qs ++ [enc ls b 0 gs] ++ fs').reverse ∈ˢ
            app mot (enc ls b 0 fs') := fun fs' hf => by
        have hfl := FFit.length_eq (M := MJ) (ls := ls) hf
        rw [← hmot, app_clam (hencS fs' hf), hF fs' hf, hgd _ hfl]
        exact (ext_field hM S hle₁ ht hc hq (hext fs' hf) hi).1
      rw [show M (b.recName 0) = M₃ MJ b (b.recName 0) from hrec,
        S.rec_val_core h2 h3 hη hl hqJ (zs := [enc ls b 0 gs]) (d := b.nparams + 1) rfl _ mot _
            hg hmotS hH,
        hgd _ (FFit.length_eq (M := MJ) (ls := ls) hg)]
  obtain ⟨q, c', fs, hq', hfs, -, rfl⟩ := S.mem_carrier_inv hl hqJ hd0 hi0 (hSv ▸ hx)
  obtain ⟨rfl, rfl⟩ := hq0 hq'
  have hpv : projVals M ls nm qs (enc ls b 0 fs) = fs := by
    apply List.ext_getElem (by simp [projVals, hlen, FFit.length_eq (M := MJ) (ls := ls) hfs])
    intro j h1 h2
    simp only [projVals, List.getElem_map, List.getElem_range]
    rw [key j (by simpa [projVals, hlen] using h1) fs hfs]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rw [hpv]

theorem etaRuleP_scoped (hC : CanonR M env (RBlock.plain b) MJ envJ envJ₁) (hle₁ : envJ₁ ≤ env)
    (R : ProjRec env b t c nm) :
    Scoped (Dom env) 0 (b.etaRuleP (nm.getD · .anonymous) c).lhs ∧
      Scoped (Dom env) 0 (b.etaRuleP (nm.getD · .anonymous) c).rhs ∧
      Scoped (Dom env) 0 (b.etaRuleP (nm.getD · .anonymous) c).type := by
  obtain ⟨ht, hc, hlen, hk, -⟩ := R
  have S : Setting MJ envJ envJ₁ b := hC.setting
  have hd0 : 0 < b.ntypes := by simp [SBlock.ntypes, ht]
  have hP : ∀ x, Dom envJ₁ x → Dom env x := fun x h => Dom.mono hle₁ h
  have hT : Dom env (b.types[0]!).name := hP _ (S.type_dom hd0)
  have hD : ∀ j (h : j < (b.params ++ [appN (.const (b.types[0]!).name (ownLevels b.uvars))
      (vars b.nparams 0 b.nparams)]).length), Scoped (Dom env) (0 + j)
      (b.params ++ [appN (.const (b.types[0]!).name (ownLevels b.uvars))
          (vars b.nparams 0 b.nparams)])[j] := by
    intro j hj
    rw [Nat.zero_add, List.getElem_append]
    split
    · next h => simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h] using
        S.params_scoped hP h
    · next h =>
      obtain rfl : j = b.nparams := by simp at hj; simp [SBlock.nparams] at h ⊢; omega
      simpa [SBlock.nparams] using Scoped.appN (f := .const (b.types[0]!).name (ownLevels b.uvars))
          (Scoped.const hT)
        (Scoped.vars (P := Dom env) (d := b.nparams) (L := 0) (n := b.nparams) (by omega))
  have hDl : (b.params ++ [appN (.const (b.types[0]!).name (ownLevels b.uvars))
      (vars b.nparams 0 b.nparams)]).length =
      b.nparams + 1 := by simp; rfl
  have hcn := (slotCtor_struct hC ht hc).1
  refine ⟨Scoped.lamTel hD (by rw [hDl, Nat.zero_add]; exact Scoped.var (by omega)),
      Scoped.lamTel hD ?_,
    Scoped.forallTel hD ?_⟩
  · rw [hDl, Nat.zero_add]
    refine Scoped.appN (Scoped.const hcn) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · exact Scoped.vars (by omega) a ha
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      have hjn : j < nm.length := by rw [hlen]; exact List.mem_range.mp hj
      unfold SBlock.projApp
      refine Scoped.appN (Scoped.const (show Dom env _ by rw [Dom, hk j hjn]; simp)) fun a ha => ?_
      rcases List.mem_append.mp ha with ha | ha
      · exact Scoped.vars (by omega) a ha
      · rw [List.mem_singleton.mp ha]; exact Scoped.var (by omega)
  · rw [hDl, Nat.zero_add]
    exact Scoped.appN (Scoped.const hT) (Scoped.vars (by omega))

theorem etaRuleP_law (hM : IsModel M env) (hC : CanonR M env (RBlock.plain b) MJ envJ envJ₁)
    (hle₁ : envJ₁ ≤ env) (R : ProjRec env b t c nm) (hη : b.etaCtor? = some c)
    (hl : ls.length = (b.etaRuleP (nm.getD · .anonymous) c).uvars) (ρ : List V) :
    interp M ls (b.etaRuleP (nm.getD · .anonymous) c).lhs ρ = interp M ls
        (b.etaRuleP (nm.getD · .anonymous) c).rhs ρ ∧
      interp M ls (b.etaRuleP (nm.getD · .anonymous) c).lhs ρ ∈ˢ
        interp M ls (b.etaRuleP (nm.getD · .anonymous) c).type ρ := by
  obtain ⟨hlS, hrS, htS⟩ := etaRuleP_scoped hC hle₁ R
  rw [interp_closed _ _ hlS.1 ρ, interp_closed _ _ hrS.1 ρ, interp_closed _ _ htS.1 ρ]
  have hl' : ls.length = b.uvars := hl
  simp only [SBlock.etaRuleP, interp_lamTel', interp_forallTel]
  refine ⟨lamTel_congr fun ws hws => ?_, lamTel_mem_piTel fun ws hws => ?_⟩ <;>
  · obtain ⟨qs, x, rfl, hq, hx⟩ := ext_delta_inv hl' R.ht hws
    have hql := Ext.length_eq M ls hq
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, List.append_nil]
    rw [interp_lastVar (n := b.nparams) hql]
    first
    | rw [etaRhs_val hM hC R hη hl' hq hx]; exact projVals_enc₀ hM hC hle₁ R hη hl' hq hx
    | have := interp_ownApp (M := M) hl' (b.types[0]!).name (zs := [x]) hql []
      simp only [List.length_singleton, List.append_nil, List.map_nil, List.reverse_append,
          List.reverse_singleton,
        List.singleton_append] at this
      rw [this]; simpa [R.ht] using hx

end Proj

end Soulgem.Nested
