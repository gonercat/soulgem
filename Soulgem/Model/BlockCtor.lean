import Soulgem.Model.BlockBound

/-! # Constructor typing -/

namespace Soulgem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V]

namespace BlockSem
variable {M : CInterp V} {ls : List Nat} {b : SBlock} {ρp : List V}

theorem enc_mem (hK : HK b) (hs : HSmall M ls b ρp) (hB : HBound M ls b ρp) {m : Nat}
    (hm : m < b.ntypes) {q : Nat} {c : SCtor} (hc : (ctorsOf b m)[q]? = some c) {fs : List V}
    (hfit : FFit M ls (carrier M ls b ρp) c.fields ρp fs)
    (hi : cidx M ls ρp c fs ∈ˢ Is M ls b ρp m) :
    enc ls b q fs ∈ˢ app (carrier M ls b ρp m) (cidx M ls ρp c fs) := by
  rw [app_carrier hK hs hB hm hi]
  unfold enc
  by_cases h0 : lev ls b = 0
  · rw [ite_eq_left h0]; exact (mem_fib_zero h0).mpr ⟨rfl, q, fs, c, hc, hfit, rfl⟩
  · rw [ite_eq_right h0]; exact (mem_fib_pos h0).mpr ⟨q, fs, ⟨c, hc, hfit, rfl⟩, rfl⟩

end BlockSem

theorem piTel_pointwise {M : CInterp V} {ls : List Nat} {B : List V → V} :
    ∀ {As Bs : List VExpr} {ρ : List V}, As.length = Bs.length →
    (∀ i (h : i < As.length) (h' : i < Bs.length) (zs : List V), Ext M ls (Bs.take i) ρ zs →
      interp M ls As[i] (zs.reverse ++ ρ) = interp M ls Bs[i] (zs.reverse ++ ρ)) →
    piTel M ls As B ρ = piTel M ls Bs B ρ
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | A :: As, B' :: Bs, ρ, hl, h => by
    simp only [piTel]
    have h0 := h 0 (by simp) (by simp) [] .nil
    simp only [List.reverse_nil, List.nil_append, List.getElem_cons_zero] at h0
    rw [h0]
    refine cpi_congr fun x hx => piTel_pointwise (by simpa using hl) fun i hi hi' zs hzs => ?_
    have := h (i + 1) (by simp; omega) (by simp; omega) (x :: zs) (by simpa using Ext.cons hx hzs)
    simpa using this

namespace BlockModel
open BlockSem

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

variable (M ls b) in
noncomputable def ctorVal (M' : CInterp V) (ls : List Nat) (q : Nat) (c : SCtor) : V :=
  Soulgem.lamTel M' ls b.params (fun ρ =>
    Soulgem.lamTel M' ls (c.fields.map (·.ty))
      (fun ρ' => enc ls b q ((ρ'.take c.fields.length).reverse)) ρ) []

theorem ctor_typed {ls : List Nat} (hl : ls.length = b.uvars) {j : Nat} (hj : j < b.ntypes)
    {q : Nat} {c : SCtor} (hcq : (ctorsOf b j)[q]? = some c) :
    ctorVal b (M₁ M b fun ls ρp => carrier M ls b ρp) ls q c ∈ˢ
      interp (M₁ M b fun ls ρp => carrier M ls b ρp) ls c.type [] := by
  have hc : c ∈ (b.types[j]!).ctors := List.mem_of_getElem? hcq
  have hC := carrier_tupleFn M b
  have hM₁ := (S.model₁ hC).1
  obtain ⟨Ps, hPl, hty, hPd⟩ := S.ctor_shape j hj c hc
  have hidxl := (S.ctorSyn hj hc).idx_len
  have hidxm := (S.ctorSyn hj hc).idx_free
  have hidxty := (S.ctorOK j hj c hc).idx_typed
  have hctx := S.fctx_consts hj hc c.fields.length (Nat.le_refl _)
  have hfctx : fctx b c c.fields.length = (b.params ++ c.fields.map (·.ty)).reverse := by
    simp [fctx]
  rw [hty, interp_forallTel]
  rw [piTel_pointwise (Bs := b.params) (by rw [hPl]; rfl) fun i hi hi' zs hzs => by
    obtain ⟨_, hd⟩ := hPd i (by rw [← hPl]; exact hi)
    have hsat := Sat.of_ext (Γ := []) (ρ := []) trivial hzs
    have := (hM₁.sound hd ls _ (by simpa using hsat)).1
    have e1 : Ps[i]! = Ps[i] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    have e2 : b.params[i]! = b.params[i] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
    rw [e1, e2] at this
    simpa using this]
  unfold ctorVal
  refine lamTel_mem_piTel fun ps hps₁ => ?_
  rw [interp_forallTel]
  refine lamTel_mem_piTel fun fs hfs₁ => ?_
  simp only [List.append_nil] at hfs₁ ⊢
  have hps : Ext M ls b.params [] ps :=
    (Ext.congrM (fun _ h => h) fun A hA => (S.free₀ (C := fun ls ρp => carrier M ls b ρp)
      (S.params_consts' A hA)).mono fun _ h => h.symm).mpr hps₁
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M ls hps]; rfl
  have hflen : fs.length = c.fields.length := by
    rw [Ext.length_eq _ ls hfs₁]; simp
  have hsatP : Sat (M₁ M b fun ls ρp => carrier M ls b ρp) ls b.params.reverse ps.reverse := by
    simpa using Sat.of_ext (Γ := []) (ρ := []) trivial hps₁
  have hsatF := Sat.of_ext hsatP hfs₁
  have hsat : Sat (M₁ M b fun ls ρp => carrier M ls b ρp) ls (fctx b c c.fields.length)
      (fs.reverse ++ ps.reverse) := by
    rw [hfctx]; simpa using hsatF
  have htk : (fs.reverse ++ ps.reverse).take c.fields.length = fs.reverse :=
    List.take_append_of_le_length (by simp [hflen]) |>.trans (List.take_of_length_le
        (by simp [hflen]))
  rw [htk, List.reverse_reverse]
  have hrev : fs.reverse ++ ps.reverse = (ps ++ fs).reverse := by simp
  have htake : (ps ++ fs).take b.nparams = ps := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hfit := BlockModel.idx_fit_gen (M := M) hM₁ (Γ := (b.params ++ c.fields.map (·.ty)).reverse)
    (zs := ps ++ fs) (by rw [← hrev, ← hfctx]; exact hsat)
    (n := b.nparams) (E := c.fields.length) (by simp [hplen, hflen]) hidxl
    (fun l hl' => by
      have := hidxty l hl'
      rw [idxType_eq] at this
      exact this)
    (fun l hl' => S.indices_closed hj hl') (fun A hA => S.free₀ (S.indices_consts hj A hA))
  rw [htake] at hfit
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
  rw [hrev, interp_indApp S.nodup hl hj (by simp [hplen, hflen]) (by omega)
      (by rw [htake]; exact hps)
    (by rw [htake]; exact hfit), htake, e]
  rw [e] at hfit
  have hfitF : FFit M ls (carrier M ls b ps.reverse) c.fields ps.reverse fs := by
    have := (S.ffit_iff_sat hC hl hj hc hps c.fields.length (Nat.le_refl _) fs hflen).mpr hsat
    simpa using this
  exact enc_mem (S.hK) (S.hSmall hl hps) (S.hBound hl hps) hj hcq hfitF
    (mkTower_mem_extSet M ls hfit)

end Setting
end BlockModel
end Soulgem
