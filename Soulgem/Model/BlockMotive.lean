import Soulgem.Model.BlockPlace
import Soulgem.Model.BlockSetting

/-! # Motives -/

namespace Soulgem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V]

/-! ## Transfer of telescopes between models -/

theorem ext_transfer {M₁ M₂ : CInterp V} {ls₁ ls₂ : List Nat} :
    ∀ {As Bs : List VExpr} {ρ₁ ρ₂ zs : List V}, As.length = Bs.length →
    (∀ i (h : i < As.length) (h' : i < Bs.length) (ys : List V), Ext M₂ ls₂ (Bs.take i) ρ₂ ys →
      interp M₁ ls₁ As[i] (ys.reverse ++ ρ₁) = interp M₂ ls₂ Bs[i] (ys.reverse ++ ρ₂)) →
    (Ext M₁ ls₁ As ρ₁ zs ↔ Ext M₂ ls₂ Bs ρ₂ zs)
  | [], [], _, _, zs, _, _ => by simp [Ext_nil_iff]
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl
  | A :: As, B :: Bs, ρ₁, ρ₂, zs, hl, h => by
    have h0 := h 0 (by simp) (by simp) [] .nil
    simp only [List.reverse_nil, List.nil_append, List.getElem_cons_zero] at h0
    constructor
    · intro hz
      cases hz with
      | cons hx hxs =>
        rw [h0] at hx
        refine .cons hx ((ext_transfer (by simpa using hl) fun i hi hi' ys hys => ?_).mp hxs)
        have := h (i + 1) (by simp; omega) (by simp; omega) (_ :: ys)
            (by simpa using Ext.cons hx hys)
        simpa using this
    · intro hz
      cases hz with
      | cons hx hxs =>
        refine .cons (h0 ▸ hx) ((ext_transfer (by simpa using hl) fun i hi hi' ys hys =>
            ?_).mpr hxs)
        have := h (i + 1) (by simp; omega) (by simp; omega) (_ :: ys)
            (by simpa using Ext.cons hx hys)
        simpa using this

theorem piTel_transfer {M₁ M₂ : CInterp V} {ls₁ ls₂ : List Nat} {B₁ B₂ : List V → V} :
    ∀ {As Bs : List VExpr} {ρ₁ ρ₂ : List V}, As.length = Bs.length →
    (∀ i (h : i < As.length) (h' : i < Bs.length) (ys : List V), Ext M₂ ls₂ (Bs.take i) ρ₂ ys →
      interp M₁ ls₁ As[i] (ys.reverse ++ ρ₁) = interp M₂ ls₂ Bs[i] (ys.reverse ++ ρ₂)) →
    (∀ ys, Ext M₂ ls₂ Bs ρ₂ ys → B₁ (ys.reverse ++ ρ₁) = B₂ (ys.reverse ++ ρ₂)) →
    piTel M₁ ls₁ As B₁ ρ₁ = piTel M₂ ls₂ Bs B₂ ρ₂
  | [], [], _, _, _, _, hB => by simpa [piTel] using hB [] .nil
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | A :: As, B :: Bs, ρ₁, ρ₂, hl, h, hB => by
    simp only [piTel]
    have h0 := h 0 (by simp) (by simp) [] .nil
    simp only [List.reverse_nil, List.nil_append, List.getElem_cons_zero] at h0
    rw [h0]
    refine cpi_congr fun x hx => piTel_transfer (by simpa using hl) (fun i hi hi' ys hys => ?_)
      fun ys hys => ?_
    · have := h (i + 1) (by simp; omega) (by simp; omega) (x :: ys) (by simpa using Ext.cons hx hys)
      simpa using this
    · have := hB (x :: ys) (.cons hx hys)
      simpa using this

namespace BlockModel
open BlockSem

theorem pull_σ1 (b : SBlock) {ps mid zs : List V} (hp : ps.length = b.nparams) {D : Nat}
    (hD : ps.length + mid.length = D) (a : Nat) (hz : zs.length = a) :
    ((List.range (b.nparams + a)).map fun L => (ps ++ mid ++ zs).getD (b.σ1 D L) pt) =
        ps ++ zs := by
  apply List.ext_getElem (by simp [hp, hz])
  intro L h1 h2
  simp only [List.getElem_map, List.getElem_range, SBlock.σ1]
  have h2' : L < ps.length + zs.length := by simpa using h2
  by_cases hL : L < b.nparams
  · rw [ite_eq_left hL, List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_left (by omega), List.getElem_append_left (by omega),
      List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [ite_eq_right hL, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
      List.getElem_append_right (by omega)]
    have e : L - b.nparams + D - (ps ++ mid).length = L - ps.length := by simp; omega
    rw [e, List.getElem?_eq_getElem (by omega)]
    rfl

variable (M : CInterp V) (b : SBlock) in
noncomputable def motSp (lb : List Nat) (ps : List V) (r j : Nat) : V :=
  piTel M lb (b.types[j]!).indices (fun ρ =>
    cpi (app (carrier M lb b ps.reverse j) (mkTower (ρ.take (b.types[j]!).indices.length).reverse))
      fun _ => univ r) ps.reverse

abbrev blev (b : SBlock) (ls' : List Nat) : List Nat := b.blockLevels.map (VLevel.eval ls')

def elimLev (b : SBlock) (ls' : List Nat) : Nat := if b.large then ls'.getD 0 0 else 0

theorem blev_length (b : SBlock) (ls' : List Nat) : (blev b ls').length = b.uvars := by
  simp [SBlock.blockLevels]

theorem interp_elimSort (M' : CInterp V) (b : SBlock) (ls' : List Nat) (ρ : List V) :
    interp M' ls' b.elimSort ρ = univ (elimLev b ls') := by
  unfold SBlock.elimSort elimLev
  split <;> simp [interp, VLevel.eval, List.getD_eq_getElem?_getD]

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

noncomputable abbrev Mc (M : CInterp V) (b : SBlock) : CInterp V := M₁ M b fun ls ρp =>
    carrier M ls b ρp

theorem index_annOK {j : Nat} (hj : j < b.ntypes) {a : Nat}
    (ha : a < (b.types[j]!).indices.length) :
    AnnOK env₁ b.uvars (((b.types[j]!).indices.take a).reverse ++ b.params.reverse)
      ((b.types[j]!).indices[a]!) := by
  revert ha; rw [getElem!_types hj]; intro ha
  obtain ⟨u, h⟩ := ((S.hwf.types _ (List.getElem_mem hj)).1 a ha).2
  have h' := h.mono S.le₁
  rw [List.reverse_append] at h'
  exact ⟨u, h'⟩

theorem interp_motiveTy {ls' : List Nat} {ps : List V} (hps : Ext M (blev b ls') b.params [] ps)
    {j : Nat} (hj : j < b.ntypes) {mots₀ : List V} (hm0 : mots₀.length = j) :
    interp (Mc M b) ls' (b.motiveTy j) (mots₀.reverse ++ ps.reverse) =
      motSp M b (blev b ls') ps (elimLev b ls') j := by
  have hC := carrier_tupleFn M b
  have hM₁ := (S.model₁ hC).1
  have hl := blev_length b ls'
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hps₁ : Ext (Mc M b) (blev b ls') b.params [] ps :=
    (Ext.congrM (M := M) (M' := Mc M b) (fun _ h => h) fun A hA =>
        (S.free₀ (S.params_consts' A hA)).mono
      fun _ h => h.symm).mp hps
  unfold SBlock.motiveTy motSp
  simp only []
  rw [interp_forallTel]
  refine piTel_transfer (by simp) (fun a ha ha' zs hzs => ?_) fun zs hzs => ?_
  · have ha2 := ha'
    have hza : zs.length = a := by
      rw [Ext.length_eq M _ hzs, List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt ha')
    simp only [List.getElem_map, List.getElem_range]
    have hrev : zs.reverse ++ (mots₀.reverse ++ ps.reverse) = (ps ++ mots₀ ++ zs).reverse := by simp
    rw [hrev]
    have hzs₁ : Ext (Mc M b) (blev b ls') ((b.types[j]!).indices.take a) ps.reverse zs :=
      (Ext.congrM (M := M) (M' := Mc M b) (fun _ h => h) fun A hA => (S.free₀ (S.indices_consts hj A
        (List.mem_of_mem_take hA))).mono fun _ h => h.symm).mp hzs
    have hsat0 := Sat.of_ext (by simpa using Sat.of_ext (Γ := []) (ρ := []) trivial hps₁) hzs₁
    have hΓ : CtxClosed (((b.types[j]!).indices.take a).reverse ++ b.params.reverse) := by
      have := tel_closed S.hG.1 S.params_ctx_closed (S.indices_ok hj) a
        (by have := ha2; rw [getElem!_types hj] at this; omega)
      rwa [← getElem!_types hj] at this
    rw [interp_binder_place hM₁ S.good₁.1 ls' b hΓ (b.nparams + a)
      (by simp only [List.length_append, List.length_reverse, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt ha')]; rw [Nat.add_comm]; rfl)
      (b.σ1 (b.nparams + j)) _ _ (S.index_annOK hj ha2) (ps ++ mots₀ ++ zs)
          (by simp only [List.length_append, hplen, hm0, hza])
      (fun L hL => by unfold SBlock.σ1; split <;> omega)
      (by rw [pull_σ1 b hplen (by omega) a hza]; simpa using hsat0)]
    rw [pull_σ1 b hplen (by omega) a hza, List.reverse_append]
    have e : (b.types[j]!).indices[a]! = (b.types[j]!).indices[a] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha']; rfl
    rw [e, interp_congr (S.free₀ (S.indices_consts hj _ (List.getElem_mem ha')))]
  · have hm : zs.length = (b.types[j]!).indices.length := Ext.length_eq M _ hzs
    simp only [interp, interp_elimSort]
    have htk : (zs.reverse ++ ps.reverse).take (b.types[j]!).indices.length = zs.reverse :=
      (List.take_append_of_le_length (by simp [hm])).trans (List.take_of_length_le (by simp [hm]))
    rw [htk, List.reverse_reverse]
    congr 1
    have hrev : zs.reverse ++ (mots₀.reverse ++ ps.reverse) = (ps ++ mots₀ ++ zs).reverse := by simp
    rw [hrev, interp_appN, List.map_append,
      interp_vars _ _ (by simp [hplen, hm0, hm, Nat.add_assoc]) (by omega),
      interp_vars _ _ (by simp [hplen, hm0, hm, Nat.add_assoc]) (by simp [Nat.add_assoc])]
    simp only [SBlock.tconst, interp]
    rw [show Mc M b = M₁ M b (fun ls ρp => carrier M ls b ρp) from rfl,
      getElem!_types hj, M₁_type S.nodup hj, ← getElem!_types hj]
    have e1 : ((ps ++ mots₀ ++ zs).drop 0).take b.nparams = ps := by
      simp [hplen]
    have e2 : ((ps ++ mots₀ ++ zs).drop (b.nparams + j)).take (b.types[j]!).indices.length =
        zs := by
      rw [← hm, show b.nparams + j = (ps ++ mots₀).length by simp [hplen, hm0], List.drop_left,
        List.take_length]
    rw [e1, e2, apps_former hps hzs]

omit S in
theorem hMot {ls' : List Nat} {ps : List V} (_hps : Ext M (blev b ls') b.params [] ps) {r : Nat}
    {mots : List V} (hm : ∀ j < b.ntypes, mots.getD j pt ∈ˢ motSp M b (blev b ls') ps r j) :
    HMot M (blev b ls') b ps.reverse r mots := by
  intro u hu
  obtain ⟨j, hj, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  unfold Bnd
  rw [untag_tagged]
  simp only []
  obtain ⟨is, his, rfl⟩ := (mem_extSet M _).mp hi
  rw [show nidx b j = (b.types[j]!).indices.length from rfl,
    projList_mkTower _ is (Ext.length_eq M _ his)]
  have h := apps_mem_piTel (hm j hj) his
  have htk : (is.reverse ++ ps.reverse).take (b.types[j]!).indices.length = is.reverse :=
    (List.take_append_of_le_length (by simp [Ext.length_eq M _ his])).trans
      (List.take_of_length_le (by simp [Ext.length_eq M _ his]))
  simp only [htk, List.reverse_reverse] at h
  exact app_mem_cpi h hx

end Setting
end BlockModel
end Soulgem
