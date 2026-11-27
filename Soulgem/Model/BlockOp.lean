import Soulgem.Model.Tele
import ConLeche.SetModel.Access

/-! # The operator of a certified block -/

namespace Soulgem.BlockSem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V] (M : CInterp V) (ls : List Nat) (b : SBlock) (ρp : List V)

def lev : Nat := b.level.eval ls

def ctorsOf (m : Nat) : List SCtor := (b.types[m]!).ctors

noncomputable def Is (m : Nat) : V := extSet M ls (b.types[m]!).indices ρp

noncomputable def fdom (X : Nat → V) (f : SField) (ρ : List V) : V :=
  match f.cert with
  | .plain w => interp M ls w ρ
  | .recursive xs k idx =>
    piTel M ls xs (fun ρ' => app (X k) (mkTower (idx.map (interp M ls · ρ')))) ρ

inductive FFit (X : Nat → V) : List SField → List V → List V → Prop where
  | nil {ρ} : FFit X [] ρ []
  | cons {f fs ρ x xs} : x ∈ˢ fdom M ls X f ρ → FFit X fs (x :: ρ) xs → FFit X (f :: fs) ρ (x :: xs)

noncomputable def telF (X : Nat → V) : (fs : List SField) → List V → TeleS V fs.length
  | [], _ => .nil
  | f :: fs, ρ => .cons (fdom M ls X f ρ) fun x => telF X fs (x :: ρ)

noncomputable def cidx (c : SCtor) (fs : List V) : V :=
  mkTower (c.idx.map (interp M ls · (fs.reverse ++ ρp)))

def Built (X : Nat → V) (m : Nat) (i : V) (q : Nat) (fs : List V) : Prop :=
  ∃ c, (ctorsOf b m)[q]? = some c ∧ FFit M ls X c.fields ρp fs ∧ cidx M ls ρp c fs = i

noncomputable def candQ (X : Nat → V) (m q : Nat) : V :=
  match (ctorsOf b m)[q]? with
  | some c => image (fun t => inj q t) (towerSet (lev ls b) (telF M ls X c.fields ρp))
  | none => empty

noncomputable def cand (X : Nat → V) (m : Nat) : V := natUnion (candQ M ls b ρp X m)

open Classical in
noncomputable def fib (X : Nat → V) (m : Nat) (i : V) : V :=
  if lev ls b = 0 then sep unitSet fun _ => ∃ q fs, Built M ls b ρp X m i q fs
  else sep (cand M ls b ρp X m) fun x => ∃ q fs, Built M ls b ρp X m i q fs ∧ x = inj q (mkTower fs)

noncomputable def Φ (X : Nat → V) (m : Nat) : V := graph (fib M ls b ρp X m) (Is M ls b ρp m)

variable {M ls b ρp}

/-! ## Field telescopes -/

theorem fitsS_telF {X : Nat → V} : ∀ {fs : List SField} {ρ xs : List V},
    FitsS (telF M ls X fs ρ) xs ↔ FFit M ls X fs ρ xs
  | [], ρ, [] => ⟨fun _ => .nil, fun _ => trivial⟩
  | [], ρ, _ :: _ => ⟨fun h => absurd h (by simp [telF, FitsS]), fun h => by cases h⟩
  | f :: fs, ρ, [] => ⟨fun h => absurd h (by simp [telF, FitsS]), fun h => by cases h⟩
  | f :: fs, ρ, x :: xs => by
    simp only [telF, FitsS, fitsS_telF]
    exact ⟨fun ⟨h1, h2⟩ => .cons h1 h2, fun | .cons h1 h2 => ⟨h1, h2⟩⟩

theorem FFit.length_eq {X : Nat → V} : ∀ {fs : List SField} {ρ xs : List V},
    FFit M ls X fs ρ xs → xs.length = fs.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => by simp [h.length_eq]

theorem FFit.get {X : Nat → V} : ∀ {fs : List SField} {ρ xs : List V}, FFit M ls X fs ρ xs →
    ∀ a (ha : a < fs.length) (hx : a < xs.length),
      xs[a] ∈ˢ fdom M ls X fs[a] ((xs.take a).reverse ++ ρ)
  | _, _, _, .cons h _, 0, _, _ => by simpa using h
  | _, _, _, .cons (x := x) _ h, a + 1, ha, hx => by
    have := h.get a (by simpa using ha) (by simpa using hx)
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this

theorem FFit.of_get {X : Nat → V} : ∀ {fs : List SField} {ρ xs : List V},
    xs.length = fs.length →
    (∀ a (ha : a < fs.length) (hx : a < xs.length),
      xs[a] ∈ˢ fdom M ls X fs[a] ((xs.take a).reverse ++ ρ)) → FFit M ls X fs ρ xs
  | [], _, [], _, _ => .nil
  | f :: fs, ρ, x :: xs, hl, h => by
    refine .cons (by have := h 0 (by simp) (by simp); simpa using this)
        (FFit.of_get (by simpa using hl) ?_)
    intro a ha hx
    have := h (a + 1) (by simpa using ha) (by simpa using hx)
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this

theorem FFit.transfer {X Y : Nat → V} {fs : List SField} {ρ xs : List V}
    (h : FFit M ls X fs ρ xs)
    (hd : ∀ a (ha : a < fs.length) (hx : a < xs.length),
      xs[a] ∈ˢ fdom M ls X fs[a] ((xs.take a).reverse ++ ρ) →
      xs[a] ∈ˢ fdom M ls Y fs[a] ((xs.take a).reverse ++ ρ)) :
    FFit M ls Y fs ρ xs :=
  FFit.of_get h.length_eq fun a ha hx => hd a ha hx (h.get a ha hx)

/-! ## The fibres -/

theorem mem_fib_zero {X : Nat → V} {m : Nat} {i x : V} (h0 : lev ls b = 0) :
    x ∈ˢ fib M ls b ρp X m i ↔ x = pt ∧ ∃ q fs, Built M ls b ρp X m i q fs := by
  unfold fib; rw [ite_eq_left h0, mem_sep, mem_unitSet_iff]

theorem inj_mem_cand {X : Nat → V} {m q : Nat} {c : SCtor} {fs : List V}
    (h0 : lev ls b ≠ 0) (hc : (ctorsOf b m)[q]? = some c) (hf : FFit M ls X c.fields ρp fs) :
    inj q (mkTower fs) ∈ˢ cand M ls b ρp X m := by
  unfold cand; rw [Tower.mem_natUnion]
  refine ⟨q, ?_⟩
  unfold candQ; rw [hc]
  exact SetTheory.mem_image.mpr ⟨_, (mem_towerSet_pos h0).mpr ⟨fs, fitsS_telF.mpr hf, rfl⟩, rfl⟩

theorem mem_fib_pos {X : Nat → V} {m : Nat} {i x : V} (h0 : lev ls b ≠ 0) :
    x ∈ˢ fib M ls b ρp X m i ↔ ∃ q fs, Built M ls b ρp X m i q fs ∧ x = inj q (mkTower fs) := by
  unfold fib; rw [ite_eq_right h0, mem_sep]
  constructor
  · exact fun h => h.2
  · intro ⟨q, fs, ⟨c, hc, hf, hi⟩, hx⟩
    exact ⟨hx ▸ inj_mem_cand h0 hc hf, q, fs, ⟨c, hc, hf, hi⟩, hx⟩

theorem app_Φ {X : Nat → V} {m : Nat} {i : V} (hi : i ∈ˢ Is M ls b ρp m) :
    app (Φ M ls b ρp X m) i = fib M ls b ρp X m i := app_graph hi

/-! ## Monotonicity -/

def HK (b : SBlock) : Prop :=
  ∀ m < b.ntypes, ∀ c ∈ ctorsOf b m, ∀ f ∈ c.fields, ∀ xs k idx,
    f.cert = .recursive xs k idx → k < b.ntypes

theorem app_le_of_tupleLe {w : Nat} {X Y : Nat → V} {k : Nat} (hk : k < b.ntypes)
    (hX : InTupleSpace w b.ntypes (Is M ls b ρp) X)
    (hle : TupleLe b.ntypes (Is M ls b ρp) X Y) (j : V) : app (X k) j ⊆ˢ app (Y k) j := by
  by_cases hj : j ∈ˢ Is M ls b ρp k
  · exact hle k hk j hj
  · rw [app_off_dom_of_mem_piSet (hX k hk) hj]; exact empty_subset _

theorem fdom_mono {w : Nat} {X Y : Nat → V} {f : SField} {ρ : List V}
    (hk : ∀ xs k idx, f.cert = .recursive xs k idx → k < b.ntypes)
    (hX : InTupleSpace w b.ntypes (Is M ls b ρp) X)
    (hle : TupleLe b.ntypes (Is M ls b ρp) X Y) :
    fdom M ls X f ρ ⊆ˢ fdom M ls Y f ρ := by
  unfold fdom
  split
  · exact Subset.refl _
  · rename_i xs k idx hcert
    exact piTel_mono fun _ _ => app_le_of_tupleLe (hk xs k idx hcert) hX hle _

theorem Built.mono {w : Nat} {X Y : Nat → V} (hK : HK b) {m : Nat} (hm : m < b.ntypes) {i : V}
    {q : Nat} {fs : List V}
    (hX : InTupleSpace w b.ntypes (Is M ls b ρp) X)
    (hle : TupleLe b.ntypes (Is M ls b ρp) X Y) (h : Built M ls b ρp X m i q fs) :
    Built M ls b ρp Y m i q fs := by
  obtain ⟨c, hc, hf, hi⟩ := h
  refine ⟨c, hc, hf.transfer fun a ha _ hx => fdom_mono (fun xs k idx he =>
    hK m hm c (List.mem_of_getElem? hc) _ (List.getElem_mem ha) xs k idx he) hX hle _ hx, hi⟩

theorem mono {w : Nat} (hK : HK b) :
    MonoTuple w b.ntypes (Is M ls b ρp) (Φ M ls b ρp) := by
  intro X Y hX _ hle m hm i hi x hx
  rw [app_Φ hi] at hx ⊢
  by_cases h0 : lev ls b = 0
  · obtain ⟨hx, q, fs, hB⟩ := (mem_fib_zero h0).mp hx
    exact (mem_fib_zero h0).mpr ⟨hx, q, fs, hB.mono hK hm hX hle⟩
  · obtain ⟨q, fs, hB, hx⟩ := (mem_fib_pos h0).mp hx
    exact (mem_fib_pos h0).mpr ⟨q, fs, hB.mono hK hm hX hle, hx⟩

/-! ## Formation -/

def HSmall (M : CInterp V) (ls : List Nat) (b : SBlock) (ρp : List V) : Prop :=
  lev ls b ≠ 0 → ∀ X, InTupleSpace (lev ls b) b.ntypes (Is M ls b ρp) X → ∀ m < b.ntypes,
      ∀ c ∈ ctorsOf b m,
    BoundS (lev ls b) (telF M ls X c.fields ρp)

theorem vnat_mem_univ {w : Nat} (hw : w ≠ 0) (q : Nat) : (vnat q : V) ∈ˢ univ w :=
  (univ_isTGUniverse hw).transitive
    (univ_mono (Nat.one_le_iff_ne_zero.mpr hw) _ (omega_mem_univ_succ 0)) (vnat_mem_omega q)

theorem cand_mem {X : Nat → V} {m : Nat} (h0 : lev ls b ≠ 0)
    (hs : ∀ c ∈ ctorsOf b m, BoundS (lev ls b) (telF M ls X c.fields ρp)) :
    cand M ls b ρp X m ∈ˢ (univ (lev ls b) : V) := by
  have hU := univ_isTGUniverse (V := V) h0
  refine Tower.natUnion_mem_univ_pos h0 fun q => ?_
  unfold candQ
  split
  · rename_i c hc
    have hT := towerSet_mem_univ _ (hs c (List.mem_of_getElem? hc))
    refine hU.image_mem hT fun t ht => ?_
    unfold inj; rw [spair_eq_kpair]
    exact hU.kpair_mem hT (vnat_mem_univ h0 q) (hU.transitive hT ht)
  · exact empty_mem_univ _

theorem maps (hs : HSmall M ls b ρp) :
    MapsTuple (lev ls b) b.ntypes (Is M ls b ρp) (Φ M ls b ρp) := by
  intro X hX m hm
  refine graph_mem_famSpace fun i _ => ?_
  unfold fib
  split
  · rename_i h0; rw [h0]; exact univ_sep_mem (unitSet_mem_univ 0)
  · rename_i h0; exact univ_sep_mem (cand_mem h0 (hs h0 X hX m hm))

end Soulgem.BlockSem

namespace Soulgem.BlockSem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V] {M : CInterp V} {ls : List Nat} {b : SBlock} {ρp : List V}

/-! ## Accessibility -/

variable (M ls b ρp) in
def HBound : Prop :=
  lev ls b ≠ 0 → ∃ A, A ∈ˢ (univ (lev ls b) : V) ∧ ∀ X, InTupleSpace (lev ls b) b.ntypes
      (Is M ls b ρp) X →
    ∀ m < b.ntypes, ∀ (q : Nat) (c : SCtor), (ctorsOf b m)[q]? = some c → ∀ fs,
        FFit M ls X c.fields ρp fs →
    ∀ (a : Nat) (f : SField) xs k idx, c.fields[a]? = some f → f.cert = .recursive xs k idx →
      extSet M ls xs ((fs.take a).reverse ++ ρp) ⊆ˢ A

variable (M ls ρp) in
abbrev pre (fs : List V) (a : Nat) : List V := (fs.take a).reverse ++ ρp

variable (M ls ρp) in
def Item (c : SCtor) (fs : List V) (β : V) (it : Nat × V × V) : Prop :=
  ∃ a f xs k idx ys, c.fields[a]? = some f ∧ f.cert = .recursive xs k idx ∧
    Ext M ls xs (pre ρp fs a) ys ∧ β = kpair (vnat a) (mkTower ys) ∧
    it = (k, mkTower (idx.map (interp M ls · (ys.reverse ++ pre ρp fs a))),
        ys.foldl app (fs.getD a pt))

theorem Item.unique {c : SCtor} {fs : List V} {a : Nat} {f : SField} {xs : List VExpr} {k : Nat}
    {idx : List VExpr} {ys : List V} {it : Nat × V × V} (hf : c.fields[a]? = some f)
    (hc : f.cert = .recursive xs k idx) (hys : Ext M ls xs (pre ρp fs a) ys)
    (h : Item M ls ρp c fs (kpair (vnat a) (mkTower ys)) it) :
    it = (k, mkTower (idx.map (interp M ls · (ys.reverse ++ pre ρp fs a))),
        ys.foldl app (fs.getD a pt)) := by
  obtain ⟨a', f', xs', k', idx', ys', hf', hc', hys', e, rfl⟩ := h
  obtain ⟨e1, e2⟩ := kpair_inj e
  cases vnat_inj e1
  rw [hf] at hf'; cases hf'
  rw [hc] at hc'; cases hc'
  rw [mkTower_inj (by rw [Ext.length_eq M ls hys, Ext.length_eq M ls hys']) e2]

theorem acc (hK : HK b) (h0 : lev ls b ≠ 0) {A : V}
    (hA : ∀ X, InTupleSpace (lev ls b) b.ntypes (Is M ls b ρp) X →
      ∀ m < b.ntypes, ∀ (q : Nat) (c : SCtor), (ctorsOf b m)[q]? = some c → ∀ fs,
          FFit M ls X c.fields ρp fs →
      ∀ (a : Nat) (f : SField) xs k idx, c.fields[a]? = some f → f.cert = .recursive xs k idx →
        extSet M ls xs (pre ρp fs a) ⊆ˢ A) :
    AccTuple (lev ls b) b.ntypes (Is M ls b ρp) b.ntypes (Is M ls b ρp) (Φ M ls b ρp)
      (natUnion fun a => image (fun t => kpair (vnat a) t) A) := by
  classical
  intro X hX m hm i hi x hx
  rw [app_Φ hi] at hx
  obtain ⟨q, fs, ⟨c, hc, hf, hidx⟩, rfl⟩ := (mem_fib_pos h0).mp hx
  let supp : Nat → V := fun a => match c.fields[a]? with
    | some f => match f.cert with
      | .recursive xs _ _ => image (fun t => kpair (vnat a) t) (extSet M ls xs (pre ρp fs a))
      | .plain _ => empty
    | none => empty
  have mem_supp : ∀ {β}, β ∈ˢ natUnion supp ↔ ∃ a f xs k idx ys, c.fields[a]? = some f ∧
      f.cert = .recursive xs k idx ∧ Ext M ls xs (pre ρp fs a) ys ∧
      β = kpair (vnat a) (mkTower ys) := by
    intro β
    rw [Tower.mem_natUnion]
    constructor
    · intro ⟨a, hβ⟩
      simp only [supp] at hβ
      split at hβ
      · rename_i f hfa
        split at hβ
        · rename_i xs k idx hcert
          obtain ⟨t, ht, rfl⟩ := SetTheory.mem_image.mp hβ
          obtain ⟨ys, hys, rfl⟩ := (mem_extSet M ls).mp ht
          exact ⟨a, f, xs, k, idx, ys, hfa, hcert, hys, rfl⟩
        · exact absurd hβ (not_mem_empty _)
      · exact absurd hβ (not_mem_empty _)
    · intro ⟨a, f, xs, k, idx, ys, hfa, hcert, hys, e⟩
      refine ⟨a, ?_⟩
      simp only [supp, hfa, hcert]
      exact SetTheory.mem_image.mpr ⟨_, mkTower_mem_extSet M ls hys, e⟩
  let g : V → Nat × V × V := fun β =>
    if h : ∃ it, Item M ls ρp c fs β it then Classical.choose h else (0, pt, pt)
  have hg : ∀ {β}, β ∈ˢ natUnion supp → Item M ls ρp c fs β (g β) := by
    intro β hβ
    obtain ⟨a, f, xs, k, idx, ys, hfa, hcert, hys, e⟩ := mem_supp.mp hβ
    have hex : ∃ it, Item M ls ρp c fs β it := ⟨_, a, f, xs, k, idx, ys, hfa, hcert, hys, e, rfl⟩
    simp only [g, dite_eq_left_of_eq_true (eq_true hex)]
    exact Classical.choose_spec hex
  have hlen := hf.length_eq
  have hval : ∀ {a f xs k idx ys}, c.fields[a]? = some f → f.cert = .recursive xs k idx →
      Ext M ls xs (pre ρp fs a) ys →
      ys.foldl app (fs.getD a pt) ∈ˢ app (X k) (mkTower (idx.map
          (interp M ls · (ys.reverse ++ pre ρp fs a)))) := by
    intro a f xs k idx ys hfa hcert hys
    obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.mp hfa
    have := hf.get a ha (hlen ▸ ha)
    unfold fdom at this; rw [hcert] at this
    have e : fs.getD a pt = fs[a]'(hlen ▸ ha) := by simp [List.getD_eq_getElem?_getD, hlen ▸ ha]
    rw [e]; exact apps_mem_piTel this hys
  refine ⟨natUnion supp, g, ?_, ?_, ?_⟩
  · intro β hβ
    obtain ⟨a, f, xs, k, idx, ys, hfa, hcert, hys, rfl⟩ := mem_supp.mp hβ
    rw [Tower.mem_natUnion]
    exact ⟨a, SetTheory.mem_image.mpr ⟨_, hA X hX m hm q c hc fs hf a f xs k idx hfa hcert
      _ (mkTower_mem_extSet M ls hys), rfl⟩⟩
  · intro β hβ
    obtain ⟨a, f, xs, k, idx, ys, hfa, hcert, hys, e, he⟩ := hg hβ
    rw [he]
    have hk : k < b.ntypes := hK m hm c (List.mem_of_getElem? hc) f (List.mem_of_getElem? hfa)
      xs k idx hcert
    have hy := hval hfa hcert hys
    refine ⟨hk, Classical.byContradiction fun hj => ?_, hy⟩
    rw [app_off_dom_of_mem_piSet (hX k hk) hj] at hy
    exact not_mem_empty _ hy
  · intro X' _ hX'
    rw [app_Φ hi]
    refine (mem_fib_pos h0).mpr ⟨q, fs, ⟨c, hc, ?_, hidx⟩, rfl⟩
    refine hf.transfer fun a ha hx hmem => ?_
    have hfa : c.fields[a]? = some c.fields[a] := List.getElem?_eq_getElem ha
    unfold fdom at hmem ⊢
    split at hmem
    · exact hmem
    · rename_i xs k idx hcert
      refine mem_piTel_of_values hmem fun ys hys => ?_
      have hβ : kpair (vnat a) (mkTower ys) ∈ˢ natUnion supp :=
        mem_supp.mpr ⟨a, _, xs, k, idx, ys, hfa, hcert, hys, rfl⟩
      have h3 := (hX' _ hβ).2.2
      rw [Item.unique hfa hcert hys (hg hβ)] at h3
      have e : fs.getD a pt = fs[a] := by simp [List.getD_eq_getElem?_getD, hx]
      rwa [e] at h3

/-! ## The carrier -/

theorem closed (hK : HK b) (hs : HSmall M ls b ρp) (hB : HBound M ls b ρp) :
    ∃ L, IsClosedTuple (lev ls b) b.ntypes (Is M ls b ρp) (Φ M ls b ρp) L := by
  by_cases h0 : lev ls b = 0
  · have := maps (M := M) (ρp := ρp) hs; rw [h0] at this ⊢; exact closedTuple_zero this
  · obtain ⟨A, hA, hAb⟩ := hB h0
    have hU := univ_isTGUniverse (V := V) h0
    refine closed_of_acc h0 ?_ (maps hs) (acc hK h0 hAb)
    refine Tower.natUnion_mem_univ_pos h0 fun a => hU.image_mem hA fun t ht =>
      hU.kpair_mem hA (vnat_mem_univ h0 a) (hU.transitive hA ht)

variable (M ls b ρp) in
noncomputable def carrier : Nat → V := lfpTuple (lev ls b) b.ntypes (Is M ls b ρp) (Φ M ls b ρp)

theorem carrier_mem : InTupleSpace (lev ls b) b.ntypes (Is M ls b ρp) (carrier M ls b ρp) :=
  lfpTuple_mem _ _ _ _

theorem app_carrier (hK : HK b) (hs : HSmall M ls b ρp) (hB : HBound M ls b ρp) {m : Nat}
    (hm : m < b.ntypes) {i : V} (hi : i ∈ˢ Is M ls b ρp m) :
    app (carrier M ls b ρp m) i = fib M ls b ρp (carrier M ls b ρp) m i := by
  rw [← app_Φ hi]
  exact (app_lfpTuple_eq (closed hK hs hB) (mono hK) (maps hs) hm hi).symm

end Soulgem.BlockSem
