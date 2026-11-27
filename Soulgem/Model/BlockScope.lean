import Soulgem.Model.BlockRecVal

/-! # Scoping of the generated terms -/

namespace Soulgem
open ConLeche ConLeche.SetTheory Lean4Lean Spec

def Scoped (P : Name → Prop) (k : Nat) (e : VExpr) : Prop := e.ClosedN k ∧ ConstsIn P e

namespace Scoped
variable {P : Name → Prop}

theorem const {k : Nat} {c : Name} {us : List VLevel} (h : P c) : Scoped P k (.const c us) :=
  ⟨trivial, h⟩

theorem sort {k : Nat} {u : VLevel} : Scoped P k (.sort u) := ⟨trivial, trivial⟩

theorem app {k : Nat} {f a : VExpr} (hf : Scoped P k f) (ha : Scoped P k a) :
    Scoped P k (.app f a) :=
  ⟨⟨hf.1, ha.1⟩, ⟨hf.2, ha.2⟩⟩

theorem forallE {k : Nat} {A B : VExpr} (hA : Scoped P k A) (hB : Scoped P (k + 1) B) :
    Scoped P k (.forallE A B) := ⟨⟨hA.1, hB.1⟩, ⟨hA.2, hB.2⟩⟩

theorem lam {k : Nat} {A B : VExpr} (hA : Scoped P k A) (hB : Scoped P (k + 1) B) :
    Scoped P k (.lam A B) := ⟨⟨hA.1, hB.1⟩, ⟨hA.2, hB.2⟩⟩

theorem var {d L : Nat} (h : L < d) : Scoped P d (var d L) :=
  ⟨by simp only [Spec.var, VExpr.ClosedN]; omega, trivial⟩

theorem vars {d L n : Nat} (h : L + n ≤ d) : ∀ a ∈ Spec.vars d L n, Scoped P d a := by
  intro a ha
  simp only [Spec.vars, List.mem_map, List.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact var (by omega)

theorem appN {k : Nat} : ∀ {f : VExpr} {as : List VExpr}, Scoped P k f → (∀ a ∈ as, Scoped P k a) →
    Scoped P k (Spec.appN f as)
  | _, [], hf, _ => hf
  | f, a :: as, hf, ha =>
    show Scoped P k (Spec.appN (.app f a) as) from
      appN (f := .app f a) (as := as) (app hf (ha a List.mem_cons_self))
        fun x hx => ha x (List.mem_cons_of_mem _ hx)

theorem forallTel : ∀ {As : List VExpr} {R : VExpr} {k : Nat},
    (∀ i (h : i < As.length), Scoped P (k + i) As[i]) → Scoped P (k + As.length) R →
    Scoped P k (Spec.forallTel As R)
  | [], _, _, _, hR => hR
  | A :: As, R, k, h, hR => forallE (h 0 (by simp)) (forallTel (fun i hi => by
      have := h (i + 1) (by simp; omega); simpa [Nat.add_assoc, Nat.add_comm 1] using this)
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hR))

theorem lamTel : ∀ {As : List VExpr} {R : VExpr} {k : Nat},
    (∀ i (h : i < As.length), Scoped P (k + i) As[i]) → Scoped P (k + As.length) R →
    Scoped P k (Spec.lamTel As R)
  | [], _, _, _, hR => hR
  | A :: As, R, k, h, hR => lam (h 0 (by simp)) (lamTel (fun i hi => by
      have := h (i + 1) (by simp; omega); simpa [Nat.add_assoc, Nat.add_comm 1] using this)
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hR))

theorem tel_append {As Bs : List VExpr} {k : Nat}
    (hA : ∀ i (h : i < As.length), Scoped P (k + i) As[i])
    (hB : ∀ i (h : i < Bs.length), Scoped P (k + As.length + i) Bs[i]) :
    ∀ i (h : i < (As ++ Bs).length), Scoped P (k + i) (As ++ Bs)[i] := by
  intro i h
  by_cases hi : i < As.length
  · rw [List.getElem_append_left hi]; exact hA i hi
  · rw [List.getElem_append_right (by omega)]
    have := hB (i - As.length) (by simp at h; omega)
    rwa [show k + As.length + (i - As.length) = k + i by omega] at this

theorem tel_congr {As Bs : List VExpr} {k : Nat} (h : As = Bs)
    (hB : ∀ i (h : i < Bs.length), Scoped P (k + i) Bs[i]) :
    ∀ i (h : i < As.length), Scoped P (k + i) As[i] := by
  subst h; exact hB

theorem tel_map_range {n k : Nat} {f : Nat → VExpr} (h : ∀ i < n, Scoped P (k + i) (f i)) :
    ∀ i (hi : i < ((List.range n).map f).length), Scoped P (k + i) ((List.range n).map f)[i] := by
  intro i hi
  simp only [List.getElem_map, List.getElem_range]
  exact h i (by simpa using hi)

end Scoped

theorem closedN_remap (g : Nat → Nat) {N N' : Nat} (hg : ∀ i < N, g i < N') :
    ∀ (e : VExpr) (k : Nat), e.ClosedN (N + k) → (remap g e k).ClosedN (N' + k)
  | .bvar i, k, h => by
    simp only [remap]; split
    · simp only [VExpr.ClosedN]; omega
    · simp only [VExpr.ClosedN] at h ⊢; have := hg (i - k) (by omega); omega
  | .sort _, _, _ | .const _ _, _, _ => by simp [remap, VExpr.ClosedN]
  | .app f a, k, h => ⟨closedN_remap g hg f k h.1, closedN_remap g hg a k h.2⟩
  | .lam A b, k, h => ⟨closedN_remap g hg A k h.1, closedN_remap g hg b (k + 1) h.2⟩
  | .forallE A b, k, h => ⟨closedN_remap g hg A k h.1, closedN_remap g hg b (k + 1) h.2⟩

theorem closedN_consumeAnn (e : VExpr) {k : Nat} (h : e.ClosedN k) : (consumeAnn e).ClosedN k := by
  unfold consumeAnn
  split
  · exact closedN_consumeAnn _ h.1.2
  · exact closedN_consumeAnn _ h.1.2
  · exact closedN_consumeAnn _ h.2
  · exact closedN_consumeAnn _ h.2
  · exact h

namespace Scoped
variable {P : Name → Prop}

theorem place {d0 d : Nat} {σ : Nat → Nat} {e : VExpr} (he : Scoped P d0 e)
    (hσ : ∀ L < d0, σ L < d) : Scoped P d (Spec.place d0 σ d e) := by
  refine ⟨?_, (constsIn_place _ _ _ _).mpr he.2⟩
  have := closedN_remap (fun i => d - 1 - σ (d0 - 1 - i)) (N := d0) (N' := d)
    (fun i hi => by have := hσ (d0 - 1 - i) (by omega); omega) e 0 he.1
  simpa [Spec.place] using this

theorem sh (b : SBlock) {k : Nat} {e : VExpr} (he : Scoped P k e) : Scoped P k (b.sh e) :=
  ⟨he.1.instL, constsIn_sh b he.2⟩

theorem binder (b : SBlock) {k : Nat} {e : VExpr} (he : Scoped P k e) : Scoped P k (b.binder e) :=
  ⟨closedN_consumeAnn _ he.1.instL, constsIn_binder b he.2⟩

end Scoped

theorem flatMap_range_forall {α : Type _} (F : Nat → List α) (Q : Nat → α → Prop) :
    ∀ {K : Nat}, (∀ j < K, ∀ q (hq : q < (F j).length),
      Q (((List.range j).map fun i => (F i).length).sum + q) (F j)[q]) →
    ∀ l (hl : l < ((List.range K).flatMap F).length), Q l ((List.range K).flatMap F)[l]
  | 0, _, l, hl => by simp at hl
  | K + 1, h, l, hl => by
    have hlen : ((List.range K).flatMap F).length = ((List.range K).map fun i =>
        (F i).length).sum := by
      rw [List.length_flatMap]
    have e : (List.range (K + 1)).flatMap F = (List.range K).flatMap F ++ F K := by
      rw [List.range_succ, List.flatMap_append]; simp
    simp only [e] at hl ⊢
    by_cases hlt : l < ((List.range K).flatMap F).length
    · rw [List.getElem_append_left hlt]
      exact flatMap_range_forall F Q (fun j hj q hq => h j (by omega) q hq) l hlt
    · rw [List.getElem_append_right (by omega)]
      have hq : l - ((List.range K).flatMap F).length < (F K).length := by simp at hl; omega
      have := h K (by omega) _ hq
      rwa [← hlen, Nat.add_sub_cancel' (by omega)] at this

universe u
variable {V : Type u} [SetTheory V]

namespace BlockModel
open BlockSem

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S
variable {P : Name → Prop} (hP : ∀ x, Dom env₁ x → P x)
include hP

theorem params_scoped {i : Nat} (hi : i < b.nparams) : Scoped P i b.params[i]! := by
  have hi' : i < b.params.length := hi
  have hc := tel_entry_closed S.hG.1 (Γ0 := []) trivial S.params_ok hi'
  have e : b.params[i]! = b.params[i] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
  rw [e]
  exact ⟨by simpa using hc, (S.params_consts' _ (List.getElem_mem hi')).mono fun x h =>
    hP x (Dom.mono S.le₁ h)⟩

theorem index_scoped {j : Nat} (hj : j < b.ntypes) {a : Nat}
    (ha : a < (b.types[j]!).indices.length) :
    Scoped P (b.nparams + a) (b.types[j]!).indices[a]! := by
  have ha' : a < (b.types[j]'hj).indices.length := by rwa [← getElem!_types hj]
  have hc := tel_entry_closed S.hG.1 S.params_ctx_closed (S.indices_ok hj) ha'
  have e : (b.types[j]!).indices[a]! = (b.types[j]'hj).indices[a] := by
    rw [List.getElem!_eq_getElem?_getD, getElem!_types hj, List.getElem?_eq_getElem ha']; rfl
  rw [e]
  have hc' := hc
  simp only [List.length_reverse] at hc'
  refine ⟨hc', ?_⟩
  have := S.indices_consts hj _ (by rw [getElem!_types hj]; exact List.getElem_mem ha')
  exact this.mono fun x h => hP x (Dom.mono S.le₁ h)

theorem field_scoped {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors)
    {a : Nat} (ha : a < c.fields.length) : Scoped P (b.nparams + a) (c.fields[a]!).ty := by
  have h := (S.field_ok hj hc ha).1
  have hcl := S.fctx_closed hj hc a (Nat.le_of_lt ha)
  have hlen : (fctx b c a).length = b.nparams + a := by
    simp only [fctx, List.length_reverse, List.length_append, List.length_map, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt ha)]; rfl
  have := (h.closedN' S.good₁.1 hcl).1
  rw [hlen] at this
  exact ⟨this, (IsDefEq.constsIn S.good₁.2 h (S.fctx_consts hj hc a (Nat.le_of_lt ha))).1.mono hP⟩

theorem xs_scoped {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors)
    {a : Nat} (ha : a < c.fields.length) {xs : List VExpr} {k : Nat} {idx : List VExpr}
    (hcert : (c.fields[a]!).cert = .recursive xs k idx) {e : Nat} (he : e < xs.length) :
    Scoped P (b.nparams + a + e) xs[e]! := by
  obtain ⟨_, _, hxs, _, _, hcl, _⟩ := S.rec_field hj hc ha hcert
  have h := hcl (e + 1) he
  rw [List.take_add_one, List.getElem?_eq_getElem he, Option.toList_some, List.reverse_append,
    List.reverse_singleton, List.singleton_append, List.cons_append] at h
  have hlen : ((xs.take e).reverse ++ fctx b c a).length = b.nparams + a + e := by
    simp only [fctx, List.length_append, List.length_reverse, List.length_map, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt ha), Nat.min_eq_left (Nat.le_of_lt he)]
    show e + (b.nparams + a) = b.nparams + a + e; omega
  have e' : xs[e]! = xs[e] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem he]; rfl
  rw [e']
  refine ⟨?_, (hxs _ (List.getElem_mem he)).1.mono hP⟩
  have h2 : xs[e].ClosedN ((xs.take e).reverse ++ fctx b c a).length := h.2
  rwa [hlen] at h2

theorem motiveTy_scoped {j : Nat} (hj : j < b.ntypes) : Scoped P (b.nparams + j)
    (b.motiveTy j) := by
  unfold SBlock.motiveTy
  simp only []
  refine Scoped.forallTel (Scoped.tel_map_range fun a ha => ?_) ?_
  · exact Scoped.binder b (Scoped.place (S.index_scoped hP hj ha)
      fun L hL => by unfold SBlock.σ1; split <;> omega)
  · simp only [List.length_map, List.length_range]
    refine Scoped.forallE (Scoped.appN (Scoped.const (hP _ (S.type_dom hj))) fun x hx =>
        ?_) Scoped.sort
    rcases List.mem_append.mp hx with h | h
    · exact Scoped.vars (by omega) x h
    · exact Scoped.vars (by omega) x h

theorem minorTy_scoped {j q : Nat} {c : SCtor} (hcq : (ctorsOf b j)[q]? = some c) (hPc : P c.name)
    {D : Nat} (hD : b.nparams + b.ntypes ≤ D) : Scoped P D (b.minorTy j c D) := by
  have hj := lt_of_ctor hcq
  have hc : c ∈ (b.types[j]!).ctors := List.mem_of_getElem? hcq
  obtain ⟨hidxl, hidx⟩ := S.ctor_idx hj hc
  unfold SBlock.minorTy
  simp only []
  refine Scoped.forallTel (Scoped.tel_append (Scoped.tel_map_range fun a ha => ?_)
    (Scoped.tel_map_range fun r hr => ?_)) ?_
  · exact Scoped.binder b (Scoped.place (S.field_scoped hP hj hc ha)
      fun L hL => by unfold SBlock.σ1; split <;> omega)
  · simp only [List.length_map, List.length_range]
    have hR : c.recFields[r]! = c.recFields[r] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hr]; rfl
    rw [hR]
    rcases hx : c.recFields[r] with ⟨a, xs, k, idx⟩
    have hmem : (a, xs, k, idx) ∈ c.recFields := hx ▸ List.getElem_mem hr
    obtain ⟨ha, hcert⟩ := recFields_mem hmem
    simp only at ha hcert
    obtain ⟨hk, _, _, hidxR, _, _, hidxc⟩ := S.rec_field hj hc ha hcert
    simp only []
    refine Scoped.forallTel (Scoped.tel_map_range fun e he => ?_) ?_
    · exact Scoped.binder b (Scoped.place (S.xs_scoped hP hj hc ha hcert he)
        fun L hL => by unfold SBlock.σ2; split; omega; split <;> omega)
    · simp only [List.length_map, List.length_range]
      refine Scoped.app (Scoped.appN (Scoped.var (by omega)) fun t ht => ?_)
        (Scoped.appN (Scoped.var (by omega)) (Scoped.vars (by omega)))
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact Scoped.sh b (Scoped.place ⟨hidxc t0 ht0, (hidxR t0 ht0).1.mono hP⟩
        fun L hL => by unfold SBlock.σ2; split; omega; split <;> omega)
  · simp only [List.length_append, List.length_map, List.length_range]
    rw [show D + (c.fields.length + c.recFields.length) = D + c.fields.length + c.recFields.length
      by omega]
    refine Scoped.app (Scoped.appN (Scoped.var (by omega)) fun t ht => ?_)
      (Scoped.appN (Scoped.const hPc) fun x hx => ?_)
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      obtain ⟨htc, htd, _⟩ := hidx t0 ht0
      exact Scoped.sh b (Scoped.place ⟨htc, htd.mono hP⟩
        fun L hL => by unfold SBlock.σ1; split <;> omega)
    · rcases List.mem_append.mp hx with h | h
      · exact Scoped.vars (by omega) x h
      · exact Scoped.vars (by omega) x h

theorem preTel_scoped (hPc : ∀ j < b.ntypes, ∀ (q : Nat) (c : SCtor), (ctorsOf b j)[q]? =
    some c → P c.name) : ∀ i (h : i < b.preTel.length), Scoped P (0 + i) b.preTel[i] := by
  have hpre := preTel_eq b
  intro i h
  have key : ∀ i (h : i < ((List.range b.nparams).map (fun i => b.binder b.params[i]!) ++
      (List.range b.ntypes).map b.motiveTy ++ minorList b).length),
      Scoped P (0 + i) ((List.range b.nparams).map (fun i => b.binder b.params[i]!) ++
        (List.range b.ntypes).map b.motiveTy ++ minorList b)[i] :=
            Scoped.tel_append (P := P) (k := 0)
    (Scoped.tel_append (Scoped.tel_map_range (f := fun i => b.binder b.params[i]!) fun i hi => by
      rw [Nat.zero_add]; exact Scoped.binder b (S.params_scoped hP hi))
      (Scoped.tel_map_range (f := b.motiveTy) fun j hj => by
        simp only [List.length_map, List.length_range, Nat.zero_add]; exact
            S.motiveTy_scoped hP hj))
    (fun l hl => by
      have := flatMap_range_forall (fun j =>
        (List.range (b.types[j]!).ctors.length).map fun q =>
          b.minorTy j (b.types[j]!).ctors[q]! (b.nparams + b.ntypes + b.ctorBase j + q))
        (fun l A => Scoped P (0 + (((List.range b.nparams).map fun i => b.binder b.params[i]!) ++
          (List.range b.ntypes).map b.motiveTy).length + l) A)
        (K := b.ntypes) (fun j hj q hq => by
          simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range,
            List.length_append]
          have hq' : q < (ctorsOf b j).length := by
            simp only [List.length_map, List.length_range] at hq; exact hq
          have hcq : (ctorsOf b j)[q]? = some (b.types[j]!).ctors[q]! := by
            rw [List.getElem?_eq_getElem hq']; congr 1
            rw [List.getElem!_eq_getElem?_getD, show (b.types[j]!).ctors = ctorsOf b j from rfl,
              List.getElem?_eq_getElem hq']; rfl
          have := S.minorTy_scoped hP hcq (hPc j hj q _ hcq)
            (D := b.nparams + b.ntypes + b.ctorBase j + q) (by omega)
          rw [← ctorBase_eq b (Nat.le_of_lt hj), show 0 + (b.nparams + b.ntypes) +
              (b.ctorBase j + q) =
            b.nparams + b.ntypes + b.ctorBase j + q by omega]
          exact this) l hl
      exact this)
  exact Scoped.tel_congr hpre key i h

theorem recType_scoped (hPc : ∀ j < b.ntypes, ∀ (q : Nat) (c : SCtor), (ctorsOf b j)[q]? =
    some c → P c.name) {d : Nat} (hd : d < b.ntypes) : Scoped P 0 (b.recType d) := by
  have hpl : b.preTel.length = b.pre := by
    rw [preTel_eq]; simp only [List.length_append, List.length_map, List.length_range,
      minorList_length]; rfl
  have hpre : b.pre = b.nparams + b.ntypes + b.nctors := rfl
  rw [recType_eq]
  refine Scoped.forallTel (Scoped.tel_append (Scoped.tel_append (S.preTel_scoped hP hPc)
    (Scoped.tel_map_range fun a ha => ?_)) fun i hi => ?_) ?_
  · rw [hpl, Nat.zero_add]
    exact Scoped.binder b (Scoped.place (S.index_scoped hP hd ha)
      fun L hL => by unfold SBlock.σ1; split <;> omega)
  · simp only [List.length_singleton] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [List.length_append, List.length_map, List.length_range, hpl, List.getElem_singleton,
      Nat.zero_add, Nat.add_zero]
    refine Scoped.appN (Scoped.const (hP _ (S.type_dom hd))) fun x hx => ?_
    rcases List.mem_append.mp hx with h | h
    · exact Scoped.vars (L := 0) (n := b.nparams) (by omega) x h
    · exact Scoped.vars (L := b.pre) (n := (b.types[d]!).indices.length) (by omega) x h
  · simp only [List.length_append, List.length_map, List.length_range, List.length_singleton, hpl,
      Nat.zero_add]
    refine Scoped.app (Scoped.appN (Scoped.var (by omega)) (Scoped.vars (by omega)))
      (Scoped.var (by omega))

end Setting

theorem preTel_length (b : SBlock) : b.preTel.length = b.pre := by
  rw [preTel_eq]; simp only [List.length_append, List.length_map, List.length_range,
    minorList_length]; rfl

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S
variable {P : Name → Prop} (hP : ∀ x, Dom env₁ x → P x)
include hP

theorem iota_scoped (hPc : ∀ j < b.ntypes, ∀ (q : Nat) (c : SCtor), (ctorsOf b j)[q]? =
    some c → P c.name)
    (hPr : ∀ k < b.ntypes, P (b.recName k)) {d q : Nat} {c : SCtor}
        (hcq : (ctorsOf b d)[q]? = some c) :
    Scoped P 0 (b.iota d q).lhs ∧ Scoped P 0 (b.iota d q).rhs ∧ Scoped P 0 (b.iota d q).type := by
  have hd := lt_of_ctor hcq
  have hc : c ∈ (b.types[d]!).ctors := List.mem_of_getElem? hcq
  have hc' : (b.types[d]!).ctors[q]! = c := by
    rw [List.getElem!_eq_getElem?_getD, show (b.types[d]!).ctors = ctorsOf b d from rfl, hcq]; rfl
  have hpre : b.pre = b.nparams + b.ntypes + b.nctors := rfl
  have hlt := ctorBase_add_lt hcq
  obtain ⟨hidxl, hidx⟩ := S.ctor_idx hd hc
  unfold SBlock.iota SBlock.rulePieces
  simp only [hc', List.length_map, List.length_range]
  have hΔ : ∀ i (h : i < (b.preTel ++ (List.range c.fields.length).map fun a =>
      b.sh (place (b.nparams + a) (b.σ1 b.pre) (b.pre + a) (c.fields[a]!).ty)).length),
      Scoped P (0 + i) (b.preTel ++ (List.range c.fields.length).map fun a =>
        b.sh (place (b.nparams + a) (b.σ1 b.pre) (b.pre + a) (c.fields[a]!).ty))[i] :=
    Scoped.tel_append (S.preTel_scoped hP hPc) (Scoped.tel_map_range fun a ha => by
      rw [preTel_length, Nat.zero_add]
      exact Scoped.sh b (Scoped.place (S.field_scoped hP hd hc ha)
        fun L hL => by unfold SBlock.σ1; split <;> omega))
  have hlen : (b.preTel ++ (List.range c.fields.length).map fun a =>
      b.sh (place (b.nparams + a) (b.σ1 b.pre) (b.pre + a) (c.fields[a]!).ty)).length =
      b.pre + c.fields.length := by
    simp only [List.length_append, List.length_map, List.length_range, preTel_length]
  have hidxP : ∀ t ∈ c.idx.map (fun t => b.sh (place (b.nparams + c.fields.length) (b.σ1 b.pre)
      (b.pre + c.fields.length) t)), Scoped P (b.pre + c.fields.length) t := by
    intro t ht
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
    obtain ⟨htc, htd, _⟩ := hidx t0 ht0
    exact Scoped.sh b (Scoped.place ⟨htc, htd.mono hP⟩
      fun L hL => by unfold SBlock.σ1; split <;> omega)
  have hintro : Scoped P (b.pre + c.fields.length) (appN (.const c.name b.blockLevels)
      (vars (b.pre + c.fields.length) 0 b.nparams ++ vars (b.pre + c.fields.length) b.pre
          c.fields.length)) := by
    refine Scoped.appN (Scoped.const (hPc d hd q c hcq)) fun x hx => ?_
    rcases List.mem_append.mp hx with h | h
    · exact Scoped.vars (L := 0) (n := b.nparams) (by omega) x h
    · exact Scoped.vars (L := b.pre) (n := c.fields.length) (by omega) x h
  refine ⟨Scoped.lamTel hΔ ?_, Scoped.lamTel hΔ ?_, Scoped.forallTel hΔ ?_⟩ <;>
      rw [Nat.zero_add, hlen]
  · refine Scoped.app (Scoped.appN (Scoped.const (hPr d hd)) fun x hx => ?_) hintro
    rcases List.mem_append.mp hx with h | h
    · exact Scoped.vars (L := 0) (n := b.pre) (by omega) x h
    · exact hidxP x h
  · refine Scoped.appN (Scoped.var (by omega)) fun x hx => ?_
    rcases List.mem_append.mp hx with h | h
    · exact Scoped.vars (L := b.pre) (n := c.fields.length) (by omega) x h
    · obtain ⟨⟨a, xs, k, idx⟩, hmem, rfl⟩ := List.mem_map.mp h
      obtain ⟨ha, hcert⟩ := recFields_mem hmem
      simp only at ha hcert
      obtain ⟨hk, _, _, hidxR, _, _, hidxc⟩ := S.rec_field hd hc ha hcert
      simp only []
      refine Scoped.lamTel (Scoped.tel_map_range fun e he => ?_) ?_
      · exact Scoped.binder b (Scoped.place (S.xs_scoped hP hd hc ha hcert he)
          fun L hL => by unfold SBlock.σ2; split; omega; split <;> omega)
      · simp only [List.length_map, List.length_range]
        refine Scoped.app (Scoped.appN (Scoped.const (hPr k hk)) fun y hy => ?_)
          (Scoped.appN (Scoped.var (by omega)) (Scoped.vars (by omega)))
        rcases List.mem_append.mp hy with h | h
        · exact Scoped.vars (L := 0) (n := b.pre) (by omega) y h
        · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp h
          exact Scoped.sh b (Scoped.place ⟨hidxc t0 ht0, (hidxR t0 ht0).1.mono hP⟩
            fun L hL => by unfold SBlock.σ2; split; omega; split <;> omega)
  · exact Scoped.app (Scoped.appN (Scoped.var (by omega)) hidxP) hintro

end Setting
end BlockModel

end Soulgem
