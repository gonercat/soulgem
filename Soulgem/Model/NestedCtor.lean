import Soulgem.Model.NestedOp
import Soulgem.Model.NestedPlain

/-! # Nested blocks: an auxiliary member's constructors correspond to its container's -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

theorem _root_.Soulgem.BlockModel.Setting.constsIn_base {M : CInterp V} {env env₁ : VEnv}
    {b : SBlock} (S : Setting M env env₁ b) {e : VExpr} (h₁ : ConstsIn (Dom env₁) e)
    (hm : mentions b.names e = false) : ConstsIn (Dom env) e :=
  (h₁.and (constsIn_of_mentions hm)).mono fun _ ⟨h1, h2⟩ => S.dom_of_dom₁ h1 h2

theorem ctorCorr_spec {tr : Translated} {b : SBlock} {nuser : Nat} {F : Fam} {earlier : List Nat}
    {r : RBlock} {a : Aux} {tJ : SType} {cb cJc : SCtor}
    (h : Spec.CtorCorr tr b nuser F earlier r a tJ cb cJc) :
    cb.fields.length = cJc.fields.length ∧
    List.Forall₂ (fun e e' => e.EqL (atKey F.lv F.Ds cb.fields.length e')) cb.idx cJc.idx ∧
    ∀ k < cb.fields.length, Spec.FieldCorr tr b nuser F earlier r k cb.fields[k]!
        cJc.fields[k]! := by
  obtain ⟨-, -, hl, hi, hf⟩ := h
  refine ⟨hl, hi, fun k hk => ?_⟩
  rw [← getElem_eq_getElem! hk, ← getElem_eq_getElem! (hl ▸ hk)]
  exact hf k hk (hl ▸ hk)

structure AuxFrame (M : CInterp V) (env env₁ : VEnv) (b : SBlock) (MJ : CInterp V)
    (envJ envJ₁ : VEnv) (rec : List RBlock) (n : Nat) (tr : Translated) (a : Aux) (J : Name)
    (lv : List VLevel) (Ds : List VExpr) (r : RBlock) (m d : Nat)
    (nuser : Nat) (fams : List Fam) (ri : Nat)
    (φ earlier : List Nat) (ls : List Nat) (ps : List V)
    (XB : Nat → V) (M₂ : CInterp V) (ns ms : List Name) (us : List VLevel) : Prop where
  S : Setting M env env₁ b
  cJ : CanonR M env r MJ envJ envJ₁
  hall : AllSpec rec n tr b nuser fams
  hs : Slot rec n tr b nuser fams a J lv Ds r m d
  hn : n = b.nparams
  hm : m < r.b.ntypes
  hcc : ∀ q < (b.types[d]!).ctors.length, Spec.CtorCorr tr b nuser { ri, lv, Ds, φ } earlier r a
    (r.b.types[m]!) ((b.types[d]!).ctors[q]!) ((r.b.types[m]!).ctors[q]!)
  hl : ls.length = b.uvars
  hps : Ext M ls b.params [] ps
  hXB : InTupleSpace (lev ls b) b.ntypes (Is M ls b ps.reverse) XB
  H : RestoreHyp M₂ (M₁ M b (patch M b ls ps.reverse XB)) ls tr [] ns ms us n (· = ps)
  hsafe : ∀ q < (b.types[d]!).ctors.length, ∀ k < ((b.types[d]!).ctors[q]!).fields.length,
    restoreSafe ns ms us n (((b.types[d]!).ctors[q]!).fields[k]!).ty (n + k) = true
  hM₂ : ∀ q < (b.types[d]!).ctors.length, ∀ k < ((b.types[d]!).ctors[q]!).fields.length,
    ConstsIn (fun c => M₂ c = M₁ M b (patch M b ls ps.reverse XB) c)
      (((b.types[d]!).ctors[q]!).fields[k]!).ty
  hlJ : (lv.map (VLevel.eval ls)).length = r.b.uvars
  hpsJ : Ext MJ (lv.map (VLevel.eval ls)) r.b.params []
    (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse).reverse

namespace AuxFrame
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} {MJ : CInterp V} {envJ envJ₁ : VEnv}
  {rec : List RBlock} {n : Nat} {tr : Translated} {a : Aux} {J : Name} {lv : List VLevel}
  {Ds : List VExpr} {r : RBlock} {m d : Nat} {ls : List Nat} {ps : List V} {XB : Nat → V}
  {M₂ : CInterp V} {ns ms : List Name} {us : List VLevel} {nuser ri : Nat} {fams : List Fam}
      {φ earlier : List Nat}

theorem fdom_corr
    (F : AuxFrame M env env₁ b MJ envJ envJ₁ rec n tr a J lv Ds r m d nuser fams ri φ earlier
        ls ps XB M₂ ns
      ms us)
    {X Y : Nat → V}
    (hX : InTupleSpace (lev ls b) b.ntypes (Is M ls b ps.reverse) X)
    (hY : InTupleSpace (lev (lv.map (VLevel.eval ls)) r.b) r.b.ntypes
      (Is MJ (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds
          ps.reverse)) Y)
    (hYle : TupleLe r.b.ntypes
      (Is MJ (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds
          ps.reverse)) Y
      (carrier MJ (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds
          ps.reverse)))
    (hXY : ∀ m' g, m' < r.b.ntypes → φ[m']? = some g → X (nuser + g) = Y m')
    (hagX : ∀ q < (b.types[d]!).ctors.length, ∀ k < ((b.types[d]!).ctors[q]!).fields.length, ∀ w,
      (((r.b.types[m]!).ctors[q]!).fields[k]!).cert = .plain w →
      ConstsIn (fun c => ∀ s < b.ntypes, (b.types[s]!).name = c → X s = XB s)
        (((b.types[d]!).ctors[q]!).fields[k]!).ty)
    {q : Nat} (hq' : q < (b.types[d]!).ctors.length) {k : Nat}
    (hk : k < ((b.types[d]!).ctors[q]!).fields.length) (ys : List V) (hys : ys.length = k)
    (hfit : FFit M ls X (((b.types[d]!).ctors[q]!).fields.take k) ps.reverse ys)
    (hfitJ : FFit MJ (lv.map (VLevel.eval ls)) Y (((r.b.types[m]!).ctors[q]!).fields.take k)
      (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse) ys) :
    fdom M ls X (((b.types[d]!).ctors[q]!).fields[k]!) (ys.reverse ++ ps.reverse) =
      fdom MJ (lv.map (VLevel.eval ls)) Y (((r.b.types[m]!).ctors[q]!).fields[k]!)
        (ys.reverse ++ keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse) := by
  have S := F.S
  have SJ := F.cJ.setting
  have hs := F.hs
  have hqJ : q < (r.b.types[m]!).ctors.length := hs.nctors ▸ hq'
  have spec := ctorCorr_spec (F.hcc q hq')
  have hmem : (b.types[d]!).ctors[q]! ∈ (b.types[d]!).ctors := getElem!_mem' hq'
  have hmemJ : (r.b.types[m]!).ctors[q]! ∈ (r.b.types[m]!).ctors := getElem!_mem' hqJ
  have hkJ : k < ((r.b.types[m]!).ctors[q]!).fields.length := spec.1 ▸ hk
  have hfc := spec.2.2 k hk
  unfold Spec.FieldCorr at hfc
  cases hcJ : (((r.b.types[m]!).ctors[q]!).fields[k]!).cert with
  | recursive xs m' idx =>
    rw [hcJ] at hfc
    cases hcb : (((b.types[d]!).ctors[q]!).fields[k]!).cert with
    | plain _ => rw [hcb] at hfc; exact hfc.elim
    | recursive xs' s idx' =>
    rw [hcb] at hfc
    obtain ⟨⟨g, hg, rfl⟩, hxs', hidx'⟩ := hfc
    obtain ⟨hm'l, _, hxsJ, hidxJ, _, _, hidxcl⟩ := SJ.rec_field F.hm hmemJ hkJ hcJ
    obtain ⟨_, _, hxsb, hidxb, _, _, _⟩ := S.rec_field hs.hd hmem hk hcb
    refine fdom_rec_corr S F.cJ (C₀ := patch M b ls ps.reverse XB) hcJ hcb hxs' hidx'
      (hXY m' g hm'l hg) (fun i hi => ?_) (fun i hi => ?_) (fun e he => ?_) (fun e he => ?_)
      (fun x hx => (hxsb x hx).1) (fun x hx => (hxsb x hx).2)
      (fun x hx => (hidxb x hx).1) (fun x hx => (hidxb x hx).2) ys hys ps.reverse
    · have h := (SJ.xs_scoped (P := Dom envJ₁) (fun _ h => h) F.hm hmemJ hkJ hcJ hi).1
      rwa [show r.b.nparams + k + i = k + i + Ds.length by rw [hs.nDs]; omega] at h
    · have hx := hxsJ _ (getElem!_mem' hi)
      exact SJ.constsIn_base hx.1 hx.2
    · have h := hidxcl e he
      rwa [show r.b.nparams + k + xs.length = k + xs.length + Ds.length by rw [hs.nDs]; omega] at h
    · exact SJ.constsIn_base (hidxJ e he).1 (hidxJ e he).2
  | plain w =>
    have hfitC := hfitJ.transfer fun i hi hx hmem' => by
      have hik : i < k := by rw [List.length_take] at hi; omega
      have hiJ : i < ((r.b.types[m]!).ctors[q]!).fields.length := by omega
      have ei : (((r.b.types[m]!).ctors[q]!).fields.take k)[i] =
          ((r.b.types[m]!).ctors[q]!).fields[i]! := by
        rw [List.getElem_take, getElem_eq_getElem! hiJ]
      rw [ei] at hmem' ⊢
      exact fdom_mono (fun xs k' idx hc => (SJ.rec_field F.hm hmemJ hiJ hc).1) hY hYle _ hmem'
    rw [hcJ] at hfc
    have hagr : ConstsIn (fun c => M₁ M b (patch M b ls ps.reverse XB) c =
        M₁ MJ r.b (carrierFn MJ r.b) c)
        (((r.b.types[m]!).ctors[q]!).fields[k]!).ty :=
      (SJ.constsIn_base (SJ.field_scoped (P := Dom envJ₁) (fun _ h => h) F.hm hmemJ hkJ).2
        hfc.2.1).mono fun c hc => by
        rw [M₁_other (S.not_name (Dom.mono F.cJ.le hc)), M₁_other (SJ.not_name hc), F.cJ.agree c hc]
    exact fdom_plain_corr S SJ hs F.hn F.hm hq' hk hkJ (F.hn ▸ hfc.1) F.hl F.hps hX F.hXB hcJ
      (hagX q hq' k hk w hcJ) F.H (F.hsafe q hq' k hk) (F.hM₂ q hq' k hk) hagr
      F.hlJ F.hpsJ ys hys hfit hfitC

theorem ctor_corr
    (F : AuxFrame M env env₁ b MJ envJ envJ₁ rec n tr a J lv Ds r m d nuser fams ri φ earlier
        ls ps XB M₂ ns
      ms us)
    {X Y : Nat → V}
    (hX : InTupleSpace (lev ls b) b.ntypes (Is M ls b ps.reverse) X)
    (hY : InTupleSpace (lev (lv.map (VLevel.eval ls)) r.b) r.b.ntypes
      (Is MJ (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds
          ps.reverse)) Y)
    (hYle : TupleLe r.b.ntypes
      (Is MJ (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds
          ps.reverse)) Y
      (carrier MJ (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds
          ps.reverse)))
    (hXY : ∀ m' g, m' < r.b.ntypes → φ[m']? = some g → X (nuser + g) = Y m')
    (hagX : ∀ q < (b.types[d]!).ctors.length, ∀ k < ((b.types[d]!).ctors[q]!).fields.length, ∀ w,
      (((r.b.types[m]!).ctors[q]!).fields[k]!).cert = .plain w →
      ConstsIn (fun c => ∀ s < b.ntypes, (b.types[s]!).name = c → X s = XB s)
        (((b.types[d]!).ctors[q]!).fields[k]!).ty) :
    CtorCorr M MJ ls (lv.map (VLevel.eval ls)) b r.b ps.reverse
      (keyArgs (M₁ M b (patch M b ls ps.reverse XB)) ls Ds ps.reverse) X Y d m := by
  have S := F.S
  have SJ := F.cJ.setting
  have hs := F.hs
  have hlen : (ctorsOf b d).length = (ctorsOf r.b m).length := hs.nctors
  refine ⟨hlen, fun q hq fs => ?_, fun q hq fs hfs => ?_⟩
  all_goals
    have hq' : q < (b.types[d]!).ctors.length := hq
    have hqJ : q < (r.b.types[m]!).ctors.length := hs.nctors ▸ hq'
    have e1 : (ctorsOf b d)[q]'hq = (b.types[d]!).ctors[q]! := getElem_eq_getElem! hq
    have e2 : (ctorsOf r.b m)[q]'(hlen ▸ hq) = (r.b.types[m]!).ctors[q]! := getElem_eq_getElem! _
    have spec := ctorCorr_spec (F.hcc q hq')
    have hmem : (b.types[d]!).ctors[q]! ∈ (b.types[d]!).ctors := getElem!_mem' hq'
    have hmemJ : (r.b.types[m]!).ctors[q]! ∈ (r.b.types[m]!).ctors := getElem!_mem' hqJ
    rw [e1, e2]
  · exact ffit_congr _ _ _ _ spec.1 (fun k hk ys hys hfit hfitJ =>
      F.fdom_corr hX hY hYle hXY hagX hq' hk ys hys hfit hfitJ) fs
  · obtain ⟨hidxlJ, hidxJ⟩ := SJ.ctor_idx F.hm hmemJ
    obtain ⟨_, hidxb⟩ := S.ctor_idx hs.hd hmem
    rw [e1] at hfs
    refine cidx_corr S F.cJ (C₀ := patch M b ls ps.reverse XB) spec.2.1 (fun e he => ?_)
      (fun e he => SJ.constsIn_base (hidxJ e he).2.1 (hidxJ e he).2.2)
      (fun x hx => (hidxb x hx).2.1) (fun x hx => (hidxb x hx).2.2) fs
      (by rw [hfs.length_eq]) ps.reverse
    have h := (hidxJ e he).1
    rwa [show r.b.nparams + ((r.b.types[m]!).ctors[q]!).fields.length =
      ((b.types[d]!).ctors[q]!).fields.length + Ds.length by rw [hs.nDs, spec.1]; omega] at h

end AuxFrame

end Soulgem.Nested
