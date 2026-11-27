import Soulgem.Model.BlockOp
import ConLeche.SetModel.GraphRec
import ConLeche.SetModel.UnionRec

/-! # The recursor of a certified block -/

namespace Soulgem.BlockSem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V] (M : CInterp V) (ls : List Nat) (b : SBlock) (ρp : List V)

noncomputable def U : V := unionSet b.ntypes (Is M ls b ρp) (carrier M ls b ρp)

open Classical in
noncomputable def enc (q : Nat) (fs : List V) : V := if lev ls b = 0 then pt else inj q (mkTower fs)

abbrev Dat (V : Type u) := Nat × Nat × List V

def Dec (u : V) (d : Dat V) : Prop :=
  ∃ i, i ∈ˢ Is M ls b ρp d.1 ∧ Built M ls b ρp (carrier M ls b ρp) d.1 i d.2.1 d.2.2 ∧
    u = tagged d.1 i (enc ls b d.2.1 d.2.2)

noncomputable def recCall (fs : List V) (a k : Nat) (idx : List VExpr) (ys : List V) : V :=
  tagged k (mkTower (idx.map (interp M ls · (ys.reverse ++ pre ρp fs a))))
      (ys.foldl app (fs.getD a pt))

noncomputable def predA (d : Dat V) (a : Nat) : V :=
  match (ctorsOf b d.1)[d.2.1]? with
  | some c => match c.fields[a]? with
    | some f => match f.cert with
      | .recursive xs k idx =>
        image (fun t => recCall M ls ρp d.2.2 a k idx (projList xs.length t))
          (extSet M ls xs (pre ρp d.2.2 a))
      | .plain _ => empty
    | none => empty
  | none => empty

noncomputable def pred (d : Dat V) : V := natUnion (predA M ls b ρp d)

open Classical in
noncomputable def untag (u : V) : Nat × V × V :=
  if h : ∃ p : Nat × V × V, u = tagged p.1 p.2.1 p.2.2 then Classical.choose h else (0, pt, pt)

def nidx (m : Nat) : Nat := (b.types[m]!).indices.length

noncomputable def Bnd (mots : List V) (u : V) : V :=
  let p := untag u
  app ((projList (nidx b p.1) p.2.1).foldl app (mots.getD p.1 pt)) p.2.2

noncomputable def ihVal (g : V) (fs : List V) (r : Nat × List VExpr × Nat × List VExpr) : V :=
  Soulgem.lamTel M ls r.2.1
    (fun ρ' => app g (recCall M ls ρp fs r.1 r.2.2.1 r.2.2.2 (ρ'.take r.2.1.length).reverse))
    (pre ρp fs r.1)

noncomputable def st (mins : List V) (d : Dat V) (g : V) : V :=
  match (ctorsOf b d.1)[d.2.1]? with
  | some c => (d.2.2 ++ c.recFields.map (ihVal M ls ρp g d.2.2)).foldl app
      (mins.getD (b.ctorBase d.1 + d.2.1) pt)
  | none => pt

noncomputable def G (r : Nat) (mots mins : List V) : V :=
  gGraph r (U M ls b ρp) (Dec M ls b ρp) (pred M ls b ρp) (Bnd b mots) (st M ls b ρp mins)

noncomputable def recAt (r : Nat) (mots mins : List V) (u : V) : V :=
    recSel (G M ls b ρp r mots mins) u

variable {M ls b ρp}

/-! ## Decoding lemmas -/

theorem untag_tagged (m : Nat) (i x : V) : untag (tagged m i x) = (m, i, x) := by
  have hex : ∃ p : Nat × V × V, tagged m i x = tagged p.1 p.2.1 p.2.2 := ⟨(m, i, x), rfl⟩
  unfold untag; rw [dite_eq_left hex]
  have hc := Classical.choose_spec hex
  generalize Classical.choose hex = p at hc ⊢
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨h1, h2, h3⟩ := tagged_inj hc
  simp only at h1 h2 h3
  rw [h1, h2, h3]

theorem mem_pred {d : Dat V} {j : V} :
    j ∈ˢ pred M ls b ρp d ↔ ∃ c a f xs k idx ys, (ctorsOf b d.1)[d.2.1]? = some c ∧
      c.fields[a]? = some f ∧ f.cert = .recursive xs k idx ∧
      Ext M ls xs (pre ρp d.2.2 a) ys ∧ j = recCall M ls ρp d.2.2 a k idx ys := by
  unfold pred; rw [Tower.mem_natUnion]
  constructor
  · intro ⟨a, h⟩
    unfold predA at h
    split at h
    · rename_i c hc
      split at h
      · rename_i f hf
        split at h
        · rename_i xs k idx hcert
          obtain ⟨t, ht, rfl⟩ := SetTheory.mem_image.mp h
          obtain ⟨ys, hys, rfl⟩ := (mem_extSet M ls).mp ht
          refine ⟨c, a, f, xs, k, idx, ys, hc, hf, hcert, hys, ?_⟩
          rw [projList_mkTower _ _ (Ext.length_eq M ls hys)]
        · exact absurd h (not_mem_empty _)
      · exact absurd h (not_mem_empty _)
    · exact absurd h (not_mem_empty _)
  · intro ⟨c, a, f, xs, k, idx, ys, hc, hf, hcert, hys, e⟩
    refine ⟨a, ?_⟩
    unfold predA; rw [hc]; simp only [hf, hcert]
    refine SetTheory.mem_image.mpr ⟨_, mkTower_mem_extSet M ls hys, ?_⟩
    rw [projList_mkTower _ _ (Ext.length_eq M ls hys)]; exact e

theorem recCall_mem_U (hK : HK b) {m q : Nat} {c : SCtor} {fs : List V} {a : Nat} {f : SField}
    {xs : List VExpr} {k : Nat} {idx : List VExpr} {ys : List V} (hm : m < b.ntypes)
    (hc : (ctorsOf b m)[q]? = some c) (hfit : FFit M ls (carrier M ls b ρp) c.fields ρp fs)
    (hf : c.fields[a]? = some f) (hcert : f.cert = .recursive xs k idx)
    (hys : Ext M ls xs (pre ρp fs a) ys) :
    recCall M ls ρp fs a k idx ys ∈ˢ U M ls b ρp := by
  obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.mp hf
  have hlen := hfit.length_eq
  have := hfit.get a ha (hlen ▸ ha)
  unfold fdom at this; rw [hcert] at this
  have hy := apps_mem_piTel this hys
  have e : fs.getD a pt = fs[a]'(hlen ▸ ha) := by simp [List.getD_eq_getElem?_getD, hlen ▸ ha]
  have hk : k < b.ntypes := hK m hm c (List.mem_of_getElem? hc) _ (List.getElem_mem ha)
      xs k idx hcert
  unfold recCall; rw [e]
  refine tagged_mem_unionSet hk ?_ hy
  refine Classical.byContradiction fun hj => ?_
  rw [app_off_dom_of_mem_piSet (carrier_mem k hk) hj] at hy
  exact not_mem_empty _ hy

theorem lt_of_ctor {m q : Nat} {c : SCtor} (h : (ctorsOf b m)[q]? = some c) : m < b.ntypes := by
  unfold ctorsOf at h
  refine Classical.byContradiction fun hm => ?_
  have e : b.types[m]? = none := List.getElem?_eq_none (by unfold SBlock.ntypes at hm; omega)
  simp only [List.getElem!_eq_getElem?_getD, e, Option.getD_none] at h
  cases h

theorem pred_sub_U (hK : HK b) {u : V} {d : Dat V} (hd : Dec M ls b ρp u d) :
    pred M ls b ρp d ⊆ˢ U M ls b ρp := by
  intro j hj
  obtain ⟨c, a, f, xs, k, idx, ys, hc, hf, hcert, hys, rfl⟩ := mem_pred.mp hj
  obtain ⟨i, _, ⟨c', hc', hfit, _⟩, rfl⟩ := hd
  rw [hc] at hc'; cases hc'
  exact recCall_mem_U hK (lt_of_ctor hc) hc hfit hf hcert hys

/-! ## The kit -/

def HMot (M : CInterp V) (ls : List Nat) (b : SBlock) (ρp : List V) (r : Nat) (mots : List V) :
    Prop :=
  ∀ u, u ∈ˢ U M ls b ρp → Bnd b mots u ∈ˢ (univ r : V)

def HMin (M : CInterp V) (ls : List Nat) (b : SBlock) (ρp : List V) (mots mins : List V) : Prop :=
  ∀ u d, Dec M ls b ρp u d → ∀ g, g ∈ˢ piSet (pred M ls b ρp d) (Bnd b mots) →
    st M ls b ρp mins d g ∈ˢ Bnd b mots u

def HUniq (M : CInterp V) (ls : List Nat) (b : SBlock) (ρp : List V) : Prop :=
  ∀ m i q q' fs fs', Built M ls b ρp (carrier M ls b ρp) m i q fs →
    Built M ls b ρp (carrier M ls b ρp) m i q' fs' → q = q' ∧ fs = fs'

theorem piSet_mono {A g : V} {B B' : V → V} (hg : g ∈ˢ piSet A B)
    (h : ∀ x, x ∈ˢ A → B x ⊆ˢ B' x) : g ∈ˢ piSet A B' := by
  rw [← eq_graph_app_of_mem_piSet hg]
  exact graph_mem_piSet fun x hx => h x hx _ (app_mem_of_mem_piSet hg hx)

theorem ind (hK : HK b) (hs : HSmall M ls b ρp) (hB : HBound M ls b ρp) :
    ∀ P : V → Prop, (∀ u, u ∈ˢ U M ls b ρp →
      (∃ d, Dec M ls b ρp u d ∧ ∀ j, j ∈ˢ pred M ls b ρp d → P j) → P u) →
    ∀ u, u ∈ˢ U M ls b ρp → P u := by
  intro P hP u hu
  obtain ⟨m, hm, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  refine lfpTuple_induction (closed hK hs hB) (mono hK) (fun m i x => P (tagged m i x)) ?_ m
      hm i hi x hx
  intro m hm i hi x hx
  have hSle := sepTuple_le (lev ls b) b.ntypes (Is M ls b ρp) (Φ M ls b ρp)
    fun m i x => P (tagged m i x)
  have hSmem := sepTuple_mem (lev ls b) b.ntypes (Is M ls b ρp) (Φ M ls b ρp)
    fun m i x => P (tagged m i x)
  rw [app_Φ hi] at hx
  have key : ∀ q fs, Built M ls b ρp (sepTuple (lev ls b) b.ntypes (Is M ls b ρp) (Φ M ls b ρp) fun
      m i x => P (tagged m i x)) m i q fs → x = enc ls b q fs →
      P (tagged m i x) := by
    intro q fs hBS hxe
    obtain ⟨c, hc, hfS, hidx⟩ := hBS
    have hfT : FFit M ls (carrier M ls b ρp) c.fields ρp fs :=
      hfS.transfer fun a ha _ hmem => fdom_mono (fun xs k idx he =>
        hK m hm c (List.mem_of_getElem? hc) _ (List.getElem_mem ha) xs k idx he) hSmem hSle _ hmem
    have hxT : x ∈ˢ app (carrier M ls b ρp m) i := by
      rw [app_carrier hK hs hB hm hi]
      by_cases h0 : lev ls b = 0
      · exact (mem_fib_zero h0).mpr ⟨by rw [hxe]; simp [enc, h0], q, fs, c, hc, hfT, hidx⟩
      · exact (mem_fib_pos h0).mpr ⟨q, fs, ⟨c, hc, hfT, hidx⟩, by rw [hxe]; simp [enc, h0]⟩
    refine hP _ (tagged_mem_unionSet hm hi hxT) ⟨(m, q, fs), ⟨i, hi, ⟨c, hc, hfT, hidx⟩,
        by rw [hxe]⟩, ?_⟩
    intro j hj
    obtain ⟨c', a, f, xs, k, idx, ys, hc', hf, hcert, hys, rfl⟩ := mem_pred.mp hj
    rw [hc] at hc'; cases hc'
    obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.mp hf
    have hlen := hfS.length_eq
    have hmem := hfS.get a ha (hlen ▸ ha)
    unfold fdom at hmem; rw [hcert] at hmem
    have hy := apps_mem_piTel hmem hys
    have e : fs.getD a pt = fs[a]'(hlen ▸ ha) := by simp [List.getD_eq_getElem?_getD, hlen ▸ ha]
    have hk : k < b.ntypes := hK m hm c (List.mem_of_getElem? hc) _ (List.getElem_mem ha)
        xs k idx hcert
    unfold recCall; rw [e]
    by_cases hJ : mkTower (idx.map (interp M ls · (ys.reverse ++ pre ρp fs a))) ∈ˢ Is M ls b ρp k
    · have : sepTuple (lev ls b) b.ntypes (Is M ls b ρp) (Φ M ls b ρp)
        (fun m i x => P (tagged m i x)) k = graph (fun i => sep (app
        (lfpTuple (lev ls b) b.ntypes (Is M ls b ρp)
          (Φ M ls b ρp) k) i) (fun x => P (tagged k i x))) (Is M ls b ρp k) := rfl
      rw [this, app_graph hJ, mem_sep] at hy
      exact hy.2
    · rw [app_off_dom_of_mem_piSet (hSmem k hk) hJ] at hy
      exact absurd hy (not_mem_empty _)
  by_cases h0 : lev ls b = 0
  · obtain ⟨hx, q, fs, hBS⟩ := (mem_fib_zero h0).mp hx
    exact key q fs hBS (by rw [hx]; simp [enc, h0])
  · obtain ⟨q, fs, hBS, hx⟩ := (mem_fib_pos h0).mp hx
    exact key q fs hBS (by rw [hx]; simp [enc, h0])

theorem dec_unique (hUq : lev ls b = 0 → HUniq M ls b ρp)
    {u : V} {d d' : Dat V} (hd : Dec M ls b ρp u d) (hd' : Dec M ls b ρp u d') : d = d' := by
  obtain ⟨m, q, fs⟩ := d
  obtain ⟨m', q', fs'⟩ := d'
  obtain ⟨i, _, ⟨c, hc, hf, _⟩, rfl⟩ := hd
  obtain ⟨i', _, hB', e⟩ := hd'
  obtain ⟨e1, e2, e3⟩ := tagged_inj e
  simp only at e1 e2; subst e1; subst e2
  by_cases h0 : lev ls b = 0
  · obtain ⟨rfl, rfl⟩ := hUq h0 m i q q' fs fs' ⟨c, hc, hf, by assumption⟩ hB'
    rfl
  · simp only [enc, h0, ite_false] at e3
    obtain ⟨rfl, e4⟩ := inj_inj e3
    obtain ⟨c', hc', hf', _⟩ := hB'
    rw [hc] at hc'; cases hc'
    rw [mkTower_inj (by rw [hf.length_eq, hf'.length_eq]) e4]

noncomputable def kit (hK : HK b) (hs : HSmall M ls b ρp) (hB : HBound M ls b ρp) (r : Nat)
    (mots mins : List V) (hmot : HMot M ls b ρp r mots) (hmin : HMin M ls b ρp mots mins)
    (huq : r ≠ 0 → lev ls b = 0 → HUniq M ls b ρp) : GraphRecKit r (U M ls b ρp) (Dat V) where
  Dec := Dec M ls b ρp
  pred := pred M ls b ρp
  B := Bnd b mots
  st := st M ls b ρp mins
  hpred := fun _ _ _ hd => pred_sub_U hK hd
  hB := hmot
  hst := by
    intro u _ d hd g hg
    refine hmin u d hd g (piSet_mono hg fun j hj => ?_)
    exact fun v hv => gGraph_mem_B hmot (fun _ _ _ hd' => pred_sub_U hK hd')
      (pred_sub_U hK hd _ hj) hv
  huniq := by
    by_cases hr : r = 0
    · subst hr; exact huniq_of_prop hmot
    · exact huniq_of_dec fun u _ d d' hd hd' => dec_unique (huq hr) hd hd'
  ind := ind hK hs hB

/-! ## The recursor's laws -/

section Laws
variable (hK : HK b) (hs : HSmall M ls b ρp) (hB : HBound M ls b ρp) {r : Nat} {mots mins : List V}
  (hmot : HMot M ls b ρp r mots) (hmin : HMin M ls b ρp mots mins)
  (huq : r ≠ 0 → lev ls b = 0 → HUniq M ls b ρp)
include hK hs hB hmot hmin huq

theorem rec_mem {u : V} (hu : u ∈ˢ U M ls b ρp) : recAt M ls b ρp r mots mins u ∈ˢ Bnd b mots u :=
  (kit hK hs hB r mots mins hmot hmin huq).rec_mem_B hu

theorem rec_eq {u : V} {d : Dat V} (hu : u ∈ˢ U M ls b ρp) (hd : Dec M ls b ρp u d) :
    recAt M ls b ρp r mots mins u =
      st M ls b ρp mins d (graph (recAt M ls b ρp r mots mins) (pred M ls b ρp d)) :=
  (kit hK hs hB r mots mins hmot hmin huq).rec_eq hu hd

end Laws

end Soulgem.BlockSem
