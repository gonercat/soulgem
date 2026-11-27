import Soulgem.Model.NestedFrame
import ConLeche.SetModel.HoleClose

/-! # Nested blocks: the auxiliary carriers are the containers' carriers at the keys -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

theorem getElem!_of_some {l : List Nat} {i g : Nat} (h : l[i]? = some g) : l[i]! = g := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp h
  rw [← getElem_eq_getElem! hi, he]

theorem constsIn_of_mentions_imp {P : Name → Prop} : ∀ {e : VExpr},
    (∀ c, mentions [c] e = true → P c) → ConstsIn P e
  | .bvar _, _ | .sort _, _ => trivial
  | .const c _, h => h c (by simp [mentions])
  | .app _ _, h | .lam _ _, h | .forallE _ _, h =>
    ⟨constsIn_of_mentions_imp fun c hc => h c (by simp [mentions, hc]),
     constsIn_of_mentions_imp fun c hc => h c (by simp [mentions, hc])⟩

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
include N

theorem slot_lt {j : Nat} (hj : j < fams.length) {r : RBlock} (hr : rec[fams[j].ri]? = some r)
    {m : Nat} (hm : m < r.b.ntypes) : m < fams[j].φ.length := by
  obtain ⟨r', hr', ⟨hlen, -⟩, -⟩ := N.famsOK.1 j hj
  rw [hr, Option.some.injEq] at hr'; subst hr'; omega

theorem carrier_le {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars)
    (hps : Ext M ls b.params [] ps) :
    ∀ g, g < b.ntypes → (auxAt tr nuser g).isSome →
      FamLe (Is M ls b ps.reverse g) (carrier M ls b ps.reverse g)
          (allKeys M b rec nuser fams MJf ls ps g) := by
  have S := N.S
  refine lfpTuple_le_on (closed S.hK (S.hSmall hl hps) (S.hBound hl hps)) (mono S.hK)
    (fun g => (auxAt tr nuser g).isSome) (N.allKeys_mem ls ps) fun g hg hG => ?_
  have emix : ∀ Z : Nat → V, (∀ x, Z x = allKeys M b rec nuser fams MJf ls ps x) →
      Φ M ls b ps.reverse Z g = Φ M ls b ps.reverse (allKeys M b rec nuser fams MJf ls ps) g :=
    fun Z h => by rw [funext h]
  rw [emix _ ?_]
  rotate_left
  · intro x
    split
    · rfl
    · rename_i hx
      have hnone : auxAt tr nuser x = none := by
        cases h : auxAt tr nuser x with
        | none => rfl
        | some _ => simp [h] at hx
      rw [N.allKeys_none hnone]; rfl
  obtain ⟨a, haS⟩ := Option.isSome_iff_exists.mp hG
  obtain ⟨ha, J, lv, Ds, r, m, hs⟩ := N.auxSpec_at haS
  have hf := hs.link
  obtain ⟨j, hj, hlv, hDs, hr, -, hφ, -⟩ := id hf
  have hrm := hs.mem
  have F := N.frame ha hs hj hlv hDs hr hφ hl hps
  have SJ := (N.canon r hrm).setting
  have hm := NWF.m_lt hs
  have hkp := N.keyArgs_patch hs.dsfree ls ps ps.reverse
  have hpsJ := F.hpsJ
  have hcar := carrier_mem (M := MJf r) (ls := lv.map (VLevel.eval ls)) (b := r.b)
    (ρp := keyArgs (M₁ M b (patch M b ls ps.reverse (allKeys M b rec nuser fams MJf ls ps))) ls
        Ds ps.reverse)
  have corr := F.ctor_corr (X := allKeys M b rec nuser fams MJf ls ps)
    (Y := carrier (MJf r) (lv.map (VLevel.eval ls)) r.b
      (keyArgs (M₁ M b (patch M b ls ps.reverse (allKeys M b rec nuser fams MJf ls ps))) ls Ds
          ps.reverse))
    (N.allKeys_mem ls ps) hcar (TupleLe.refl _ _ _)
    (fun m' g hm' hg => by rw [N.allKeys_slot hj hr hg, hlv, hDs, hkp])
    (fun q _ k _ w _ => (N.S.field_scoped (P := fun _ => True) (fun _ _ => trivial) hs.hd
      (getElem!_mem' (by assumption)) (by assumption)).2.mono fun _ _ _ _ _ => rfl)
  intro i hi
  have hiJ : i ∈ˢ Is (MJf r) (lv.map (VLevel.eval ls)) r.b
      (keyArgs (M₁ M b (patch M b ls ps.reverse (allKeys M b rec nuser fams MJf ls ps))) ls Ds
          ps.reverse) m := by
    rw [← aux_Is N.S (N.canon r hrm) hs hm _ ls ps.reverse]; exact hi
  rw [app_Φ_congr (N.lev_aux hf ls) corr hi hiJ]
  have hfix := app_carrier SJ.hK (SJ.hSmall F.hlJ hpsJ) (SJ.hBound F.hlJ hpsJ) hm
    (by simpa using hiJ)
  simp only [List.reverse_reverse] at hfix
  rw [← app_Φ hiJ] at hfix
  rw [← hfix, N.allKeys_aux hs, ← hkp]
  exact Subset.refl _

theorem ge_step {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars)
    (hps : Ext M ls b.params [] ps) {j : Nat} (hj : j < fams.length) {r : RBlock}
    (hr : rec[fams[j].ri]? = some r) {m : Nat} (hm : m < r.b.ntypes)
    (IH : ∀ g ∈ images (fams.take j),
      carrier M ls b ps.reverse (nuser + g) = allKeys M b rec nuser fams MJf ls ps (nuser + g)) :
    FamLe (Is M ls b ps.reverse (nuser + fams[j].φ[m]!))
      (allKeys M b rec nuser fams MJf ls ps (nuser + fams[j].φ[m]!))
      (carrier M ls b ps.reverse (nuser + fams[j].φ[m]!)) := by
  have S := N.S
  have hrm : r ∈ rec := List.mem_of_getElem? hr
  have cJ := N.canon r hrm
  have SJ := cJ.setting
  have hφ : ∀ m' < r.b.ntypes, fams[j].φ[m']? = some (nuser + fams[j].φ[m']! - nuser) :=
    fun m' hm' => by
      have h := N.slot_lt hj hr hm'
      rw [Nat.add_sub_cancel_left, List.getElem?_eq_getElem h, getElem_eq_getElem! h]
  obtain ⟨a, ha, hs⟩ := N.slotSpec hj hr hm
  have hf := hs.link
  have haM : a ∈ tr.aux := List.mem_of_getElem? ha
  have F := N.frame haM hs hj rfl rfl hr (hφ m hm) hl hps
  have hkp := N.keyArgs_patch hs.dsfree ls ps ps.reverse
  generalize hρJ : keyArgs (M₁ M b (patch M b ls ps.reverse (allKeys M b rec nuser fams
      MJf ls ps))) ls
    fams[j].Ds ps.reverse = ρJ at hkp
  have hlev : lev ls b = lev (fams[j].lv.map (VLevel.eval ls)) r.b := N.lev_aux hf ls
  let L : Nat → V := fun m' => carrier M ls b ps.reverse (nuser + fams[j].φ[m']!)
  have hIs : ∀ m' < r.b.ntypes, Is M ls b ps.reverse (nuser + fams[j].φ[m']!) =
      Is (MJf r) (fams[j].lv.map (VLevel.eval ls)) r.b ρJ m' := fun m' hm' => by
    obtain ⟨_, _, hsp⟩ := N.slotSpec hj hr hm'
    rw [← hρJ]; exact aux_Is S cJ hsp hm' _ ls ps.reverse
  have hYmem : InTupleSpace (lev (fams[j].lv.map (VLevel.eval ls)) r.b) r.b.ntypes
      (Is (MJf r) (fams[j].lv.map (VLevel.eval ls)) r.b ρJ) L := fun m' hm' => by
    obtain ⟨_, _, hsp⟩ := N.slotSpec hj hr hm'
    simp only [L]
    rw [← hIs m' hm', ← hlev]; exact carrier_mem _ hsp.hd
  have hYle : TupleLe r.b.ntypes (Is (MJf r) (fams[j].lv.map (VLevel.eval ls)) r.b ρJ) L
      (carrier (MJf r) (fams[j].lv.map (VLevel.eval ls)) r.b ρJ) := fun m' hm' => by
    obtain ⟨a', ha', hsp⟩ := N.slotSpec hj hr hm'
    have ha'M : a' ∈ tr.aux := List.mem_of_getElem? ha'
    simp only [L]
    have hle := N.carrier_le hl hps _ hsp.hd (by rw [hsp.auxAt_eq]; rfl)
    rw [N.allKeys_aux hsp, ← hkp, hIs m' hm'] at hle
    exact hle
  have hclosed : TupleLe r.b.ntypes (Is (MJf r) (fams[j].lv.map (VLevel.eval ls)) r.b ρJ)
      (Φ (MJf r) (fams[j].lv.map (VLevel.eval ls)) r.b ρJ L) L := by
    intro m' hm' i₀ hi₀
    obtain ⟨a', ha', hsp⟩ := N.slotSpec hj hr hm'
    have hf' := hsp.link
    have ha'M : a' ∈ tr.aux := List.mem_of_getElem? ha'
    simp only [L]
    have F' := N.frame ha'M hsp hj rfl rfl hr (hφ m' hm') hl hps
    have hib : i₀ ∈ˢ Is M ls b ps.reverse (nuser + fams[j].φ[m']!) := by
      rw [hIs m' hm']; exact hi₀
    have corr := F'.ctor_corr (X := carrier M ls b ps.reverse) (Y := L) carrier_mem
      (hρJ ▸ hYmem) (hρJ ▸ hYle)
      (fun m'' g _ hg => by
        show carrier M ls b ps.reverse (nuser + g) =
          carrier M ls b ps.reverse (nuser + fams[j].φ[m'']!)
        rw [getElem!_of_some hg])
      (fun q hq k hk w hw => by
        have hfc := (ctorCorr_spec (F'.hcc q hq)).2.2 k hk
        unfold Spec.FieldCorr at hfc
        rw [hw] at hfc
        refine constsIn_of_mentions_imp fun c hc s hs hn => ?_
        cases hax : auxAt tr nuser s with
        | none => rw [N.allKeys_none hax]
        | some a'' =>
          unfold auxAt at hax
          split at hax; · cases hax
          rename_i hlt
          have hge : nuser ≤ s := Nat.le_of_not_lt hlt
          have hn'' := N.member_name hax (by omega : nuser + (s - nuser) < b.ntypes)
          rw [Nat.add_sub_cancel' hge] at hn''
          have hg := hfc.2.2 (s - nuser) a'' hax (by rw [← hn'', hn]; exact hc)
          have := IH _ hg
          rwa [Nat.add_sub_cancel' hge] at this)
    have e1 := app_Φ_congr (N.lev_aux hf' ls) corr hib (hρJ ▸ hi₀)
    have hfix := app_carrier S.hK (S.hSmall hl hps) (S.hBound hl hps) hsp.hd hib
    rw [← app_Φ hib] at hfix
    rw [hρJ] at e1
    rw [← e1, ← hfix]
    exact Subset.refl _
  have hle := lfpTuple_le (X := L) ⟨hYmem, hclosed⟩
  intro i₀ hi₀
  have hiJ : i₀ ∈ˢ Is (MJf r) (fams[j].lv.map (VLevel.eval ls)) r.b ρJ m := by
    rw [← hIs m hm]; exact hi₀
  have := hle m hm i₀ hiJ
  simp only [L] at this
  rw [N.allKeys_aux hs, ← hkp]
  exact this

theorem fam_eq {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars)
    (hps : Ext M ls b.params [] ps) (j : Nat) : ∀ (hj : j < fams.length) {r : RBlock},
    rec[fams[j].ri]? = some r → ∀ m < r.b.ntypes,
      carrier M ls b ps.reverse (nuser + fams[j].φ[m]!) =
        allKeys M b rec nuser fams MJf ls ps (nuser + fams[j].φ[m]!) := by
  induction j using Nat.strongRecOn with
  | ind j IH =>
    intro hj r hr m hm
    have hIH : ∀ g ∈ images (fams.take j), carrier M ls b ps.reverse (nuser + g) =
        allKeys M b rec nuser fams MJf ls ps (nuser + g) := by
      intro g hg
      obtain ⟨F, hF, hgF⟩ := List.mem_flatMap.mp hg
      obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hF
      have hj'j : j' < j := by simp at hj'; omega
      have hj'l : j' < fams.length := by omega
      simp only [List.getElem_take] at hgF
      obtain ⟨σ, hσ, rfl⟩ := List.getElem_of_mem hgF
      obtain ⟨r', hr', ⟨hlen, -⟩, -⟩ := N.famsOK.1 j' hj'l
      rw [getElem_eq_getElem! hσ]
      exact IH j' hj'j hj'l hr' σ (hlen ▸ hσ)
    have hge := N.ge_step hl hps hj hr hm hIH
    obtain ⟨a, ha, hs⟩ := N.slotSpec hj hr hm
    have hle := N.carrier_le hl hps _ hs.hd
      (by rw [hs.auxAt_eq]; rfl)
    exact famSpace_ext (carrier_mem _ hs.hd) (N.allKeys_mem ls ps _ hs.hd) fun t ht =>
      Subset.antisymm (hle t ht) (hge t ht)

theorem carrier_allKeys {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars)
    (hps : Ext M ls b.params [] ps) {g : Nat} (_hg : g < b.ntypes) :
    carrier M ls b ps.reverse g = allKeys M b rec nuser fams MJf ls ps g := by
  cases h : auxAt tr nuser g with
  | none => rw [N.allKeys_none h]
  | some a =>
    obtain ⟨_, J, lv, Ds, r, m, hs⟩ := N.auxSpec_at h
    obtain ⟨j, hj, -, -, hr, hge, hφ, -⟩ := hs.link
    have e : nuser + fams[j].φ[m]! = g := by rw [getElem!_of_some hφ]; omega
    rw [← e]; exact N.fam_eq hl hps j hj hr m (NWF.m_lt hs)

theorem carrier_slot {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars)
    (hps : Ext M ls b.params [] ps) {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr}
    {r : RBlock} {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d) :
    carrier M ls b ps.reverse d = carrier (MJf r) (lv.map (VLevel.eval ls)) r.b
      (keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse) m := by
  rw [N.carrier_allKeys hl hps hs.hd, N.allKeys_aux hs]

end NWF

end Soulgem.Nested
