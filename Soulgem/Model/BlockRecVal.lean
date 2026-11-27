import Soulgem.Model.BlockRecTy
import Soulgem.Model.BlockMinor
import Soulgem.Model.BlockUniq

/-! # The recursor -/

namespace Soulgem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V]

theorem Ext.append_inv {M : CInterp V} {ls : List Nat} {As Bs : List VExpr} {ρ zs : List V}
    (h : Ext M ls (As ++ Bs) ρ zs) :
    ∃ xs ys, zs = xs ++ ys ∧ Ext M ls As ρ xs ∧ Ext M ls Bs (xs.reverse ++ ρ) ys :=
  ⟨_, _, (List.take_append_drop _ _).symm, BlockModel.Ext.split h⟩

namespace BlockModel
open BlockSem

abbrev recIdx (b : SBlock) (d : Nat) : List VExpr :=
  (List.range (b.types[d]!).indices.length).map fun a =>
    b.binder (place (b.nparams + a) (b.σ1 b.pre) (b.pre + a) (b.types[d]!).indices[a]!)

abbrev recMajor (b : SBlock) (d : Nat) : VExpr :=
  appN (b.tconst d) (vars (b.pre + (b.types[d]!).indices.length) 0 b.nparams ++
    vars (b.pre + (b.types[d]!).indices.length) b.pre (b.types[d]!).indices.length)

theorem recType_eq (b : SBlock) (d : Nat) : b.recType d =
    Spec.forallTel (b.preTel ++ recIdx b d ++ [recMajor b d])
      (.app (appN (var (b.pre + (b.types[d]!).indices.length + 1) (b.nparams + d))
          (vars (b.pre + (b.types[d]!).indices.length + 1) b.pre (b.types[d]!).indices.length))
        (var (b.pre + (b.types[d]!).indices.length + 1) (b.pre + (b.types[d]!).indices.length))) :=
  rfl

theorem preTel_eq (b : SBlock) : b.preTel =
    (List.range b.nparams).map (fun i => b.binder b.params[i]!) ++
      (List.range b.ntypes).map b.motiveTy ++ minorList b := rfl

variable (M : CInterp V) (b : SBlock) in
noncomputable def recRes (ls' : List Nat) (d : Nat) (ws : List V) : V :=
  recAt M (blev b ls') b (ws.take b.nparams).reverse (elimLev b ls')
    ((ws.drop b.nparams).take b.ntypes) ((ws.drop (b.nparams + b.ntypes)).take b.nctors)
    (tagged d (mkTower ((ws.drop b.pre).take (b.types[d]!).indices.length))
      (ws.getD (b.pre + (b.types[d]!).indices.length) pt))

variable (M : CInterp V) (b : SBlock) in
noncomputable def recVal (M' : CInterp V) (d : Nat) (ls' : List Nat) : V :=
  Soulgem.lamTel M' ls' (b.preTel ++ recIdx b d ++ [recMajor b d])
    (fun ρ => recRes M b ls' d ρ.reverse) []

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem rec_typed {M' : CInterp V} (hag : ∀ x, Dom env₁ x → M' x = Mc M b x)
    (hM' : IsModel M' env₁)
    (hctor : ∀ j < b.ntypes, ∀ q c, (ctorsOf b j)[q]? = some c →
      M' c.name = fun ls => ctorVal b (Mc M b) ls q c)
    (ls' : List Nat) {d : Nat} (hd : d < b.ntypes) :
    recVal M b M' d ls' ∈ˢ interp M' ls' (b.recType d) [] := by
  have hl := blev_length b ls'
  rw [recType_eq, interp_forallTel]
  unfold recVal
  refine lamTel_mem_piTel fun xs hxs => ?_
  simp only [List.append_nil, List.reverse_reverse]
  rw [preTel_eq] at hxs
  obtain ⟨w4, x1, rfl, h4, hX⟩ := Ext.append_inv hxs
  obtain ⟨w3, is, rfl, h3, hI⟩ := Ext.append_inv h4
  obtain ⟨w2, mins, rfl, h2, hN⟩ := Ext.append_inv h3
  obtain ⟨ps, mots, rfl, hP, hT⟩ := Ext.append_inv h2
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq _ _ hP]; simp
  have hmotl : mots.length = b.ntypes := by rw [Ext.length_eq _ _ hT]; simp
  have hminl : mins.length = b.nctors := by rw [Ext.length_eq _ _ hN, minorList_length]
  have hisl : is.length = (b.types[d]!).indices.length := by rw [Ext.length_eq _ _ hI]; simp
  obtain ⟨x, rfl⟩ : ∃ x, x1 = [x] := by
    have := Ext.length_eq _ _ hX
    match x1, this with
    | [x], _ => exact ⟨x, rfl⟩
  have hpre : b.pre = b.nparams + b.ntypes + b.nctors := rfl
  have hps : Ext M (blev b ls') b.params [] ps := (S.ext_params hag hM' ps).mp hP
  have hmots : ∀ j < b.ntypes, mots.getD j pt ∈ˢ motSp M b (blev b ls') ps (elimLev b ls') j := by
    intro j hj
    have hj' : j < mots.length := by omega
    have := hT.get j (by simpa using hj) hj'
    simp only [List.getElem_map, List.getElem_range, List.append_nil] at this
    rw [S.interp_motiveTy' hag hps hj (by simp; omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    exact this
  have hmot := BlockModel.Setting.hMot hps hmots
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
    have e : (mins.take (b.ctorBase j + q)).reverse ++ ((ps ++ mots).reverse ++ []).reverse.reverse
        = (ps ++ mots ++ mins.take (b.ctorBase j + q)).reverse := by simp
    simpa using this
  have hmin := S.hMin hag hM' hctor hps hmotl (by omega) hmins
  have hD : ps.length + (mots ++ mins).length = b.pre := by simp only [List.length_append]; omega
  have hρI : mins.reverse ++ (mots.reverse ++ (ps.reverse ++ [])) =
      (ps ++ (mots ++ mins)).reverse := by
    simp
  rw [show (ps ++ mots ++ mins).reverse ++ [] = mins.reverse ++ (mots.reverse ++ (ps.reverse ++ []))
    by simp] at hI
  have hI' : Ext M' ls' (recIdx b d) (ps ++ (mots ++ mins)).reverse is := by
    have := hI; simp only [List.reverse_append, List.append_nil, List.append_assoc] at this ⊢
    exact this
  have his : Ext M (blev b ls') (b.types[d]!).indices ps.reverse is :=
    (S.ext_indices hag hM' hps hd hD is).mp hI'
  have hx : x ∈ˢ app (carrier M (blev b ls') b ps.reverse d) (mkTower is) := by
    cases hX with
    | cons hx _ =>
      have e : (ps ++ mots ++ mins ++ is).reverse ++ [] = (ps ++ (mots ++ mins) ++ is).reverse := by
        simp
      rw [e, S.interp_major hag hps hd hD his] at hx
      exact hx
  have hW : (ps ++ mots ++ mins ++ is ++ [x]).length = b.pre +
      (b.types[d]!).indices.length + 1 := by
    simp only [List.length_append, List.length_singleton]; omega
  simp only [interp]
  rw [interp_appN, interp_var _ _ hW (by omega), interp_var _ _ hW (by omega),
    interp_vars _ _ hW (by omega)]
  have e_ps : (ps ++ mots ++ mins ++ is ++ [x]).take b.nparams = ps := by
    simp [List.append_assoc, hplen]
  have e_mots : ((ps ++ mots ++ mins ++ is ++ [x]).drop b.nparams).take b.ntypes = mots := by
    simp [List.append_assoc, hplen, hmotl]
  have e_mins : ((ps ++ mots ++ mins ++ is ++ [x]).drop (b.nparams + b.ntypes)).take b.nctors
      = mins := by
    rw [show b.nparams + b.ntypes = (ps ++ mots).length by simp [hplen, hmotl]]
    simp [List.append_assoc, hminl]
  have e_is : ((ps ++ mots ++ mins ++ is ++ [x]).drop b.pre).take
      (b.types[d]!).indices.length = is := by
    rw [show b.pre = (ps ++ mots ++ mins).length by simp only [List.length_append]; omega]
    simp [List.append_assoc, hisl]
  have e_x : (ps ++ mots ++ mins ++ is ++ [x]).getD (b.pre + (b.types[d]!).indices.length)
      pt = x := by
    rw [show b.pre + (b.types[d]!).indices.length = (ps ++ mots ++ mins ++ is).length by
      simp only [List.length_append]; omega]
    simp
  have e_mot : (ps ++ mots ++ mins ++ is ++ [x]).getD (b.nparams + d) pt = mots.getD d pt := by
    simp only [List.append_assoc]
    rw [getD_append_right' (by omega), show b.nparams + d - ps.length = d by omega,
      getD_append_left' (by omega)]
  unfold recRes
  rw [e_ps, e_mots, e_mins, e_is, e_x, e_mot]
  have hu : tagged d (mkTower is) x ∈ˢ U M (blev b ls') b ps.reverse :=
    mem_unionSet.mpr ⟨d, hd, _, mkTower_mem_extSet M _ his, x, hx, rfl⟩
  have huq : elimLev b ls' ≠ 0 → lev (blev b ls') b = 0 → HUniq M (blev b ls') b ps.reverse := by
    intro hr h0
    have hlarge : b.large = true := by
      unfold elimLev at hr; split at hr
      · assumption
      · exact absurd rfl hr
    exact S.hUniq hl hps h0 hlarge
  have hrec := rec_mem S.hK (S.hSmall hl hps) (S.hBound hl hps) hmot hmin huq hu
  unfold Bnd at hrec
  rw [untag_tagged] at hrec
  simp only [] at hrec
  rw [projList_mkTower _ _ (by simp [nidx, hisl])] at hrec
  exact hrec

end Setting
end BlockModel
end Soulgem
