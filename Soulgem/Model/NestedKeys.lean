import Soulgem.Model.BlockIota
import Soulgem.Model.NestedLe

/-! # Nested blocks: an auxiliary type reads as its key -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

section Keys
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
  {MJ : CInterp V} {envJ envJ₁ : VEnv} {rec : List RBlock} {n : Nat} {tr : Translated}
  {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr} {r : RBlock} {m d : Nat}

include S in
theorem aux_keys (cJ : CanonR M env r MJ envJ envJ₁) (hs : Slot rec n tr b nuser fams a J
    lv Ds r m d) (hm : m < r.b.ntypes) (hnd : b.names.Nodup)
    {E : VEnv} {MT : CInterp V} (hMT : IsModel MT E) (hTenv : ∀ c, Dom env c → MT c = M c)
    (hkt : ArgsTyped E b.uvars b.params.reverse (r.b.params.map (·.instL lv)) Ds)
    (hlv : lv.length = r.b.uvars)
    {C : List Nat → List V → Nat → V} (hag : ∀ D ∈ Ds, ConstsIn (fun c => M₁ M b C c = MT c) D)
    {ls : List Nat} {ps : List V} (hps : Ext M ls b.params [] ps)
    (hCd : C ls ps.reverse d =
      carrier MJ (lv.map (VLevel.eval ls)) r.b (keyArgs (M₁ M b C) ls Ds ps.reverse) m) :
    ps.foldl app (M₁ M b C a.name ls) = interp (M₁ M b C) ls a.key ps.reverse := by
  have SJ := cJ.setting
  have ed : b.types[d]! = b.types[d]'hs.hd := by
    rw [← getElem_eq_getElem! hs.hd]
  have hname : a.name = (b.types[d]'hs.hd).name := by rw [← ed, hs.name]
  rw [hname, M₁_type hnd hs.hd]
  unfold former
  rw [apps_lamTel hps, List.append_nil]
  obtain ⟨k, -, he, hc, hcon, -, hread⟩ := hs.read cJ
  have hpsJ := keyArgs_ext S cJ hMT hTenv hkt hag hps
  have hat := interp_atKey (M₁ M b C) ls lv Ds ps.reverse (k := 0)
    (by rw [Nat.zero_add, hs.nDs]; exact hc) [] rfl
  simp only [List.nil_append] at hat
  rw [interp_EqL _ _ he, hat, interp_congr (hcon.mono fun c hc => M₁_other (S.not_name hc)) _,
    show keyArgs (M₁ M b C) ls Ds ps.reverse = (Ds.map (interp (M₁ M b C) ls · ps.reverse)).reverse
      from rfl, hread _ _ (by simp [hlv]) hpsJ]
  have em : r.b.types[m]! = r.b.types[m]'hm := by
    rw [← getElem_eq_getElem! hm]
  rw [em, M₁_type SJ.nodup hm]
  unfold former
  rw [apps_lamTel hpsJ, List.append_nil]
  have eρ : (Ds.map (interp (M₁ M b C) ls · ps.reverse)).reverse =
      keyArgs (M₁ M b C) ls Ds ps.reverse := rfl
  rw [eρ]
  obtain ⟨hlen, hget⟩ := EqLTel.get hs.indices
  apply lamTel_transfer hlen
  · intro i hi hi' ys hys
    have hiJ : i < (r.b.types[m]!).indices.length := hi'
    have hys' : ys.reverse.length = i := by
      rw [List.length_reverse, Ext.length_eq _ _ hys, List.length_take]; omega
    have hX : ∀ A ∈ (b.types[d]!).indices, ConstsIn (Dom env) A := S.indices_consts hs.hd
    have e1 : interp M ls (b.types[d]!).indices[i] (ys.reverse ++ ps.reverse) =
        interp (M₁ M b C) ls (b.types[d]!).indices[i] (ys.reverse ++ ps.reverse) :=
      (interp_congr ((S.free₀ (C := C) (hX _ (List.getElem_mem hi))).mono fun _ h => h.symm) _)
    have hc := SJ.indices_closed hm hiJ
    rw [← hs.nDs, Nat.add_comm, ← getElem_eq_getElem! hiJ] at hc
    rw [e1, interp_EqL _ _ (hget i hi hi') _, Nat.zero_add,
      interp_atKey (M₁ M b C) ls lv Ds ps.reverse hc ys.reverse hys']
    have hJc : ConstsIn (Dom envJ) ((r.b.types[m]!).indices[i]) :=
      SJ.indices_consts hm _ (List.getElem_mem hiJ)
    exact interp_congr (hJc.mono fun _ h => agree_J S cJ h) _
  · intro ys hys
    have hyl : ys.length = (r.b.types[m]!).indices.length := Ext.length_eq _ _ hys
    have hnd' : nidx b d = nidx r.b m := by
      unfold nidx; rw [hlen]
    rw [hCd, hnd']
    unfold nidx
    rw [List.take_left' (by simp [hyl]), List.take_left' (by simp [hyl])]

end Keys

end Soulgem.Nested
