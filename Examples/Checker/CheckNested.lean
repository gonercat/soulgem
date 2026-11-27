import Examples.Checker.CheckWF
import Soulgem.Spec.Env

/-! # A verified checker for `NestedWF` (`nestedWFB_sound`) -/

namespace Soulgem.Checker
open Lean4Lean Soulgem.Spec

instance (b : SBlock) (U n : Nat) (ts : List UType) : Decidable (b.Certifies U n ts) := by
  unfold SBlock.Certifies; infer_instance

def equivB (a b : VLevel) : Bool := leN a b && leN b a

theorem equivB_sound {a b : VLevel} (h : equivB a b = true) : a ≈ b := by
  simp only [equivB, Bool.and_eq_true] at h
  exact funext fun ls => Nat.le_antisymm (leN_sound h.1 ls) (leN_sound h.2 ls)

def all₂ (p : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => p a b && all₂ p as bs
  | _, _ => false

theorem all₂_sound {p : α → β → Bool} {P : α → β → Prop} (hp : ∀ a b, p a b = true → P a b) :
    ∀ {as : List α} {bs : List β}, all₂ p as bs = true → List.Forall₂ P as bs
  | [], [], _ => .nil
  | a :: as, b :: bs, h => by
    simp only [all₂, Bool.and_eq_true] at h
    exact .cons (hp a b h.1) (all₂_sound hp h.2)
  | [], _ :: _, h | _ :: _, [], h => by simp [all₂] at h

def eqLB : VExpr → VExpr → Bool
  | .bvar i, .bvar j => i == j
  | .sort u, .sort v => equivB u v
  | .const c us, .const d vs => c == d && all₂ equivB us vs
  | .app f a, .app g b => eqLB f g && eqLB a b
  | .lam A b, .lam B c => eqLB A B && eqLB b c
  | .forallE A b, .forallE B c => eqLB A B && eqLB b c
  | _, _ => false

theorem eqLB_sound : ∀ {a b : VExpr}, eqLB a b = true → a.EqL b
  | .bvar i, .bvar j, h => by simpa [eqLB, VExpr.EqL] using h
  | .sort u, .sort v, h => equivB_sound h
  | .const c us, .const d vs, h => by
    simp only [eqLB, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1, all₂_sound (fun _ _ => equivB_sound) h.2⟩
  | .app f a, .app g b, h | .lam f a, .lam g b, h | .forallE f a, .forallE g b, h => by
    simp only [eqLB, Bool.and_eq_true] at h
    exact ⟨eqLB_sound h.1, eqLB_sound h.2⟩
  | .bvar _, .sort _, h | .bvar _, .const .., h | .bvar _, .app .., h | .bvar _, .lam .., h
  | .bvar _, .forallE .., h | .sort _, .bvar _, h | .sort _, .const .., h | .sort _, .app .., h
  | .sort _, .lam .., h | .sort _, .forallE .., h | .const .., .bvar _, h | .const .., .sort _, h
  | .const .., .app .., h | .const .., .lam .., h | .const .., .forallE .., h
  | .app .., .bvar _, h | .app .., .sort _, h | .app .., .const .., h | .app .., .lam .., h
  | .app .., .forallE .., h | .lam .., .bvar _, h | .lam .., .sort _, h | .lam .., .const .., h
  | .lam .., .app .., h | .lam .., .forallE .., h | .forallE .., .bvar _, h
  | .forallE .., .sort _, h | .forallE .., .const .., h | .forallE .., .app .., h
  | .forallE .., .lam .., h => by simp [eqLB] at h

def eqLTelB (lv : List VLevel) (Ds : List VExpr) : Nat → List VExpr → List VExpr → Bool
  | _, [], [] => true
  | k, a :: as, b :: bs => eqLB a (atKey lv Ds k b) && eqLTelB lv Ds (k + 1) as bs
  | _, _, _ => false

theorem eqLTelB_sound {lv : List VLevel} {Ds : List VExpr} :
    ∀ {k : Nat} {as bs : List VExpr}, eqLTelB lv Ds k as bs = true → EqLTel lv Ds k as bs
  | _, [], [], _ => trivial
  | k, a :: as, b :: bs, h => by
    simp only [eqLTelB, Bool.and_eq_true] at h
    exact ⟨eqLB_sound h.1, eqLTelB_sound h.2⟩
  | _, [], _ :: _, h | _, _ :: _, [], h => by simp [eqLTelB] at h

variable (tr : Translated) (b : SBlock) (nuser : Nat)

def fieldCorrB (F : Fam) (earlier : List Nat) (r : RBlock) (k : Nat) (fb fJ : SField) : Bool :=
  match fJ.cert, fb.cert with
  | .recursive xs m idx, .recursive xs' s idx' =>
    (match F.φ[m]? with | some g => s == nuser + g | none => false) &&
    eqLTelB F.lv F.Ds k xs' xs &&
    all₂ (fun e e' => eqLB e (atKey F.lv F.Ds (k + xs.length) e')) idx' idx
  | .recursive .., .plain _ => false
  | .plain _, _ =>
    eqLB (tr.restoreBody [] b.nparams fb.ty (b.nparams + k)) (atKey F.lv F.Ds k fJ.ty) &&
    !mentions r.b.names fJ.ty &&
    (List.range tr.aux.length).all fun g => match tr.aux[g]? with
    | some a => !mentions [a.name] fb.ty || earlier.contains g
    | none => true

theorem fieldCorrB_sound {F : Fam} {earlier : List Nat} {r : RBlock} {k : Nat} {fb fJ : SField}
    (h : fieldCorrB tr b nuser F earlier r k fb fJ = true) :
    FieldCorr tr b nuser F earlier r k fb fJ := by
  unfold fieldCorrB at h
  unfold FieldCorr
  cases hJ : fJ.cert <;> cases hb : fb.cert <;> simp only [hJ, hb] at h ⊢
  rotate_left 2
  · cases h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨?_, eqLTelB_sound h2, all₂_sound (fun _ _ => eqLB_sound) h3⟩
    split at h1
    · rename_i g hg; exact ⟨g, hg, by simpa using h1⟩
    · cases h1
  all_goals
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨eqLB_sound h1, h2, fun g a ha hm => ?_⟩
    have hg : g < tr.aux.length := (List.getElem?_eq_some_iff.mp ha).1
    have := List.all_eq_true.mp h3 g (List.mem_range.mpr hg)
    simp only [ha, hm, Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
    exact this

def ctorCorrB (F : Fam) (earlier : List Nat) (r : RBlock) (a : Aux) (tJ : SType)
    (cb cJ : SCtor) : Bool :=
  cb.name == cJ.name.replacePrefix tJ.name a.name &&
  cb.name.replacePrefix a.name tJ.name == cJ.name &&
  cb.fields.length == cJ.fields.length &&
  all₂ (fun e e' => eqLB e (atKey F.lv F.Ds cb.fields.length e')) cb.idx cJ.idx &&
  (List.range cb.fields.length).all fun k => match cb.fields[k]?, cJ.fields[k]? with
    | some fb, some fJ => fieldCorrB tr b nuser F earlier r k fb fJ
    | _, _ => false

theorem ctorCorrB_sound {F : Fam} {earlier : List Nat} {r : RBlock} {a : Aux} {tJ : SType}
    {cb cJ : SCtor} (h : ctorCorrB tr b nuser F earlier r a tJ cb cJ = true) :
    CtorCorr tr b nuser F earlier r a tJ cb cJ := by
  unfold ctorCorrB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h4, all₂_sound (fun _ _ => eqLB_sound) h5, fun k hk hk' => ?_⟩
  have := List.all_eq_true.mp h6 k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk'] at this
  exact fieldCorrB_sound tr b nuser this

def famAtB (earlier : List Nat) (F : Fam) (r : RBlock) : Bool :=
  F.φ.length == r.b.ntypes && F.Ds.length == r.b.nparams && F.lv.length == r.b.uvars &&
  equivB b.level (r.b.level.inst F.lv) &&
  F.Ds.all (fun D => !mentions (keyHidden tr b nuser) D) &&
  (List.range F.φ.length).all fun σ => match F.φ[σ]? with
    | none => false
    | some g => match tr.aux[g]?, b.types[nuser + g]?, r.b.types[σ]?, r.slotKey σ with
      | some a, some t, some tJ, some key =>
        eqLB a.key (atKey F.lv F.Ds 0 key) &&
        eqLTelB F.lv F.Ds 0 t.indices tJ.indices && t.ctors.length == tJ.ctors.length &&
        (List.range t.ctors.length).all fun q => match t.ctors[q]?, tJ.ctors[q]? with
          | some cb, some cJ => ctorCorrB tr b nuser F earlier r a tJ cb cJ
          | _, _ => false
      | _, _, _, _ => false

theorem famAtB_sound {earlier : List Nat} {F : Fam} {r : RBlock}
    (h : famAtB tr b nuser earlier F r = true) : FamAt tr b nuser earlier F r := by
  unfold famAtB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hD⟩, h5⟩ := h
  have slot : ∀ σ (hσ : σ < F.φ.length), ∃ a t tJ key, tr.aux[F.φ[σ]]? = some a ∧
      b.types[nuser + F.φ[σ]]? = some t ∧ r.b.types[σ]? = some tJ ∧ r.slotKey σ = some key ∧
      a.key.EqL (atKey F.lv F.Ds 0 key) ∧ EqLTel F.lv F.Ds 0 t.indices tJ.indices ∧
      t.ctors.length = tJ.ctors.length ∧ ∀ q (h : q < t.ctors.length) (h' : q < tJ.ctors.length),
        CtorCorr tr b nuser F earlier r a tJ t.ctors[q] tJ.ctors[q] := fun σ hσ => by
    have := List.all_eq_true.mp h5 σ (List.mem_range.mpr hσ)
    simp only [List.getElem?_eq_getElem hσ] at this
    split at this
    · rename_i a t tJ key ha ht htJ hk
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      obtain ⟨⟨⟨g1, g3⟩, g4⟩, g5⟩ := this
      refine ⟨a, t, tJ, key, ha, ht, htJ, hk, eqLB_sound g1, eqLTelB_sound g3, g4,
        fun q hq hq' => ?_⟩
      have := List.all_eq_true.mp g5 q (List.mem_range.mpr hq)
      simp only [List.getElem?_eq_getElem hq, List.getElem?_eq_getElem hq'] at this
      exact ctorCorrB_sound tr b nuser this
    · cases this
  refine ⟨h1, h2, h3, equivB_sound h4, fun D hD' => by simpa using List.all_eq_true.mp hD D hD',
    fun σ hσ => ?_, fun σ hσ => ?_⟩
  · obtain ⟨a, -, -, key, ha, -, -, hk, hkey, -⟩ := slot σ hσ
    exact ⟨a, key, ha, hk, hkey⟩
  · obtain ⟨a, t, tJ, -, ha, ht, htJ, -, -, rest⟩ := slot σ hσ
    exact ⟨a, t, tJ, ha, ht, htJ, rest⟩

def argsTypedB (env₁ : VEnv) (r : RBlock) (F : Fam) : Bool :=
  let Ps := r.b.params.map (·.instL F.lv)
  F.Ds.length == Ps.length && (List.range F.Ds.length).all fun i => match F.Ds[i]?, Ps[i]? with
    | some D, some P => typedAsB env₁ b.uvars b.params.reverse D
        (subst (argSubst (F.Ds.take i)) P 0)
    | _, _ => false

theorem argsTypedB_sound {env₁ : VEnv} {r : RBlock} {F : Fam}
    (h : argsTypedB b env₁ r F = true) :
    ArgsTyped env₁ b.uvars b.params.reverse (r.b.params.map (·.instL F.lv)) F.Ds := by
  unfold argsTypedB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun i hi hi' => ?_⟩
  have := List.all_eq_true.mp h.2 i (List.mem_range.mpr hi)
  simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at this
  exact typedAsB_sound this

def famsOKB (rec : List RBlock) (env₁ : VEnv) (fams : List Fam) : Bool :=
  ((List.range fams.length).all fun j => match fams[j]? with
    | some F => match rec[F.ri]? with
      | some r => famAtB tr b nuser (images (fams.take j)) F r &&
          argsTypedB b env₁ r F
      | none => false
    | none => false) &&
  (images fams).isPerm (List.range tr.aux.length)

theorem famsOKB_sound {rec : List RBlock} {env₁ : VEnv} {fams : List Fam}
    (h : famsOKB tr b nuser rec env₁ fams = true) :
    FamsOK tr b nuser rec env₁ fams := by
  unfold famsOKB at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun j hj => ?_, List.isPerm_iff.mp h.2⟩
  have := List.all_eq_true.mp h.1 j (List.mem_range.mpr hj)
  simp only [List.getElem?_eq_getElem hj] at this
  split at this
  · rename_i r hr
    simp only [Bool.and_eq_true] at this
    exact ⟨r, hr, famAtB_sound tr b nuser this.1, argsTypedB_sound b this.2⟩
  · cases this

def nestedWFB (rec : List RBlock) (env : VEnv) (u : UDecl) (fams : List Fam) :
    Bool :=
  decide (b.Certifies u.uvars u.nparams tr.types) && b.checkWF env && RestoreSafe tr b nuser &&
  ((b.types.drop nuser).all fun t => t.ctors.all fun c => (env.constants c.name).isNone) &&
  ((List.range (b.ntypes - nuser)).all fun i => (env.constants (b.recName (nuser + i))).isNone) &&
  AuxMembers tr b nuser && RecNames b nuser && fams.all (·.kernelDs.isNone) &&
  match b.add env with
  | some envT => famsOKB tr b nuser rec envT fams
  | none => false

theorem nestedWFB_none {rec : List RBlock} {env : VEnv} {u : UDecl} {fams : List Fam}
    (h : nestedWFB tr b nuser rec env u fams = true) : ∀ F ∈ fams, F.kernelDs = none := by
  unfold nestedWFB at h
  simp only [Bool.and_eq_true] at h
  exact fun F hF => by simpa using List.all_eq_true.mp h.1.2 F hF

theorem nestedWFB_sound {rec : List RBlock} {env : VEnv} {u : UDecl} {fams : List Fam}
    (h : nestedWFB tr b nuser rec env u fams = true) : NestedWF tr b nuser rec env u fams := by
  have hnone := nestedWFB_none tr b nuser h
  unfold nestedWFB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, hw⟩, hs⟩, ha1⟩, ha2⟩, hm⟩, hr⟩, -⟩, hy⟩ := h
  refine ⟨hc, b.checkWF_sound hw, hs, ⟨ha1, ha2⟩, hm, hr, ?_⟩
  split at hy
  · rename_i envT he
    refine ⟨envT, he, ?_, fun j hj Ks hK => ?_⟩
    · rw [certTr_of_none tr hnone]
      exact famsOKB_sound tr b nuser hy
    · simp [hnone _ (List.getElem_mem hj)] at hK
  · cases hy

/-- The position in `rec` of the block declaring user type `J`. -/
def recIdx (rec : List RBlock) (J : Name) : Option Nat :=
  (List.range rec.length).find? fun i =>
    (List.range rec[i]!.nuser).any fun d => (rec[i]!.b.types[d]!).name == J

/-- Candidate families, ordered by `famAtB`; `nestedWFB` checks them. -/
def familiesFor (rec : List RBlock) (tr : Translated) (b : SBlock) (nuser : Nat) : List Fam :=
  let groups := tr.aux.foldl (init := ([] : List Fam)) fun fams a =>
    match headArgs a.key with
    | (.const J lv, Ds) => match recIdx rec J with
      | some ri =>
        if fams.any (fun F => F.ri == ri && F.lv == lv && F.Ds == Ds) then fams else
        let r := rec[ri]!
        let φ := (List.range r.b.ntypes).map fun σ => match r.slotKey σ with
          | some key => (tr.aux.findIdx? fun a' => eqLB a'.key (atKey lv Ds 0 key)).getD
              tr.aux.length
          | none => tr.aux.length
        fams ++ [{ ri, lv, Ds, φ }]
      | none => fams
    | _ => fams
  let groups := groups.filter fun F =>
    !(groups.any fun F' => !(F'.ri == F.ri && F'.lv == F.lv && F'.Ds == F.Ds) &&
      F.φ.all fun g => g < tr.aux.length && F'.φ.contains g)
  let passes (done : List Fam) (F : Fam) : Bool := match rec[F.ri]? with
    | some r => famAtB tr b nuser (images done) F r
    | none => false
  let rec order : Nat → List Fam → List Fam → List Fam
    | 0, done, rest => done ++ rest
    | n + 1, done, rest => match rest.findIdx? (passes done) with
      | some i => order n (done ++ [rest[i]!]) (rest.eraseIdx i)
      | none => done ++ rest
  order groups.length [] groups

end Soulgem.Checker
