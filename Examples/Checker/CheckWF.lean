import Examples.Checker.LevelDec
import Checks.KReduce
import Examples.Checker.Restored
import Soulgem.Spec.WF
import Soulgem.Model.Level

/-! # A verified checker for `SBlock.WF` without conversion (`checkWF_sound`) -/

namespace Soulgem.Checker
open Lean4Lean Soulgem.Spec Soulgem.Checks

variable (env : VEnv) (U : Nat)

/-- The sort of `e`'s inferred type, when that type is a sort. -/
def sortOfInfer (Γ : List VExpr) (e : VExpr) : Option VLevel :=
  match Checks.infer env U Γ e with
  | some (.sort u) => some u
  | _ => none

variable {env U} in
theorem sortOfInfer_sound {Γ : List VExpr} {e : VExpr} {u : VLevel}
    (h : sortOfInfer env U Γ e = some u) : env.HasType U Γ e (.sort u) := by
  unfold sortOfInfer at h
  split at h
  · rename_i hT; cases h; exact Checks.infer_sound hT
  · cases h

/-- `e : Sort u`, its inferred sort equivalent to `u`. -/
def hasSortB (Γ : List VExpr) (e : VExpr) (u : VLevel) : Bool :=
  match sortOfInfer env U Γ e with
  | some u' => decide (u'.WF U) && decide (u.WF U) && levelEqB u' u
  | none => false

variable {env U} in
theorem hasSortB_sound {Γ : List VExpr} {e : VExpr} {u : VLevel}
    (h : hasSortB env U Γ e u = true) : env.HasType U Γ e (.sort u) := by
  unfold hasSortB at h
  split at h
  · rename_i u' hu
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨w', w⟩, he⟩ := h
    exact .defeqDF (.sortDF (of_decide_eq_true w') (of_decide_eq_true w) (levelEqB_sound he))
        (sortOfInfer_sound hu)
  · cases h

/-- Π-telescopes with equal binders ending in sorts of equivalent levels. -/
def sortTelB : VExpr → VExpr → Bool
  | .forallE A B, .forallE A' B' => decide (A = A') && sortTelB B B'
  | .sort l, .sort l' => decide (l'.WF U) && leN l l' && leN l' l
  | _, _ => false

theorem sortTelB_sound : ∀ {Γ : List VExpr} {A B T : VExpr}, Checks.infer env U Γ A = some T →
    sortTelB U A B = true → DefEqTy env U Γ A B := by
  intro Γ A
  induction A generalizing Γ with
  | forallE A B _ ihB =>
    intro B' T hi h
    cases B' with
    | forallE A' B'' =>
      simp only [sortTelB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [Checks.infer] at hi
      split at hi
      · rename_i u v hA hB
        obtain ⟨w, hw⟩ := ihB hB h
        exact ⟨_, .forallEDF (Checks.infer_sound hA) hw⟩
      · cases hi
    | _ => simp [sortTelB] at h
  | sort l =>
    intro B' T hi h
    cases B' with
    | sort l' =>
      simp only [sortTelB, Bool.and_eq_true] at h
      obtain ⟨⟨hw, h1⟩, h2⟩ := h
      simp only [Checks.infer] at hi
      split at hi
      · rename_i hl
        exact ⟨_, .sortDF hl (of_decide_eq_true hw)
          (funext fun ls => Nat.le_antisymm (leN_sound h1 ls) (leN_sound h2 ls))⟩
      · cases hi
    | _ => simp [sortTelB] at h
  | _ => intro B' T _ h; cases B' <;> simp [sortTelB] at h

/-- `DefEqTy` by `defEqTyB` or `sortTelB`. -/
def defEqTyLB (Γ : List VExpr) (A B : VExpr) : Bool :=
  defEqTyB env U Γ A B || (match Checks.infer env U Γ A with
      | some _ => sortTelB U A B | none => false)

variable {env U} in
theorem defEqTyLB_sound {Γ : List VExpr} {A B : VExpr} (h : defEqTyLB env U Γ A B = true) :
    DefEqTy env U Γ A B := by
  unfold defEqTyLB at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact defEqTyB_sound h
  · split at h
    · rename_i T hT; exact sortTelB_sound env U hT h
    · cases h

/-- `e : A` by inference, then syntax or `sortTelB`. -/
def typedAsB (Γ : List VExpr) (e A : VExpr) : Bool :=
  match Checks.infer env U Γ e with
  | some T => decide (T = A) || (match Checks.infer env U Γ T with
      | some _ => sortTelB U T A | none => false)
  | none => false

variable {env U} in
theorem typedAsB_sound {Γ : List VExpr} {e A : VExpr} (h : typedAsB env U Γ e A = true) :
    env.HasType U Γ e A := by
  unfold typedAsB at h
  split at h
  · rename_i T hT
    have he := Checks.infer_sound hT
    rcases Bool.or_eq_true_iff.mp h with h | h
    · rw [← of_decide_eq_true h]; exact he
    · split at h
      · rename_i T' hT'
        obtain ⟨_, hd⟩ := sortTelB_sound env U hT' h
        exact .defeqDF hd he
      · cases h
  · cases h

theorem eval_of_isAlwaysZero' : ∀ {l : VLevel}, l.isAlwaysZero = true → ∀ ls, l.eval ls = 0
  | .zero, _, _ => rfl
  | .max a b, h, ls => by
    simp only [VLevel.isAlwaysZero, Bool.and_eq_true] at h
    simp [VLevel.eval, eval_of_isAlwaysZero' h.1 ls, eval_of_isAlwaysZero' h.2 ls]
  | .imax _ b, h, ls => by
    simp only [VLevel.isAlwaysZero] at h
    simp [VLevel.eval, Lean.Nat.imax, eval_of_isAlwaysZero' h ls]
  | .succ _, h, _ | .param _, h, _ => by simp [VLevel.isAlwaysZero] at h

end Soulgem.Checker

namespace Soulgem.Spec.SBlock
open Lean4Lean Soulgem.Checker Soulgem.Checks
variable (b : SBlock)

def fieldB (env : VEnv) (Γ : List VExpr) (d : Nat) (f : SField) : Bool :=
  match f.cert with
  | .plain w => defEqTyB env b.uvars Γ f.ty w
  | .recursive xs k idx =>
    defEqTyB env b.uvars Γ f.ty (forallTel xs (b.indApp k (d + xs.length) idx)) &&
    (List.range xs.length).all (fun e => annB env b.uvars ((xs.take e).reverse ++ Γ) xs[e]!) &&
    (List.range idx.length).all (fun l => hasTypeB env b.uvars (xs.reverse ++ Γ) idx[l]!
      (b.idxType k (d - b.nparams + xs.length) idx l)) &&
    (List.range xs.length).all fun e =>
      match sortOfInfer env b.uvars ((xs.take e).reverse ++ Γ) xs[e]! with
      | some u => b.level.isAlwaysZero || leN u b.level
      | none => false

def ctorB (env : VEnv) (j : Nat) (c : SCtor) : Bool :=
  isTypeB env b.uvars [] c.type &&
  (List.range b.nparams).all (fun i =>
    defEqTyB env b.uvars (b.params.take i).reverse (c.paramTys b.nparams)[i]! b.params[i]!) &&
  (List.range c.idx.length).all (fun l =>
    hasTypeB env b.uvars (b.params ++ c.fields.map (·.ty)).reverse c.idx[l]!
      (b.idxType j c.fields.length c.idx l)) &&
  (List.range c.fields.length).all fun a =>
    hasSortB env b.uvars (b.fieldCtx c a) (c.fields[a]!).ty (c.fields[a]!).sort &&
    annB env b.uvars (b.fieldCtx c a) (c.fields[a]!).ty &&
    (b.level.isAlwaysZero || leN (c.fields[a]!).sort b.level) &&
    b.fieldB env (b.fieldCtx c a) (b.nparams + a) (c.fields[a]!)

def checkWF (env : VEnv) : Bool :=
  decide b.Syn && decide (b.level.WF b.uvars) &&
  (List.range b.nparams).all (fun i =>
    isTypeB env b.uvars (b.params.take i).reverse b.params[i]! &&
    annB env b.uvars (b.params.take i).reverse b.params[i]!) &&
  b.types.all (fun t =>
    (List.range t.indices.length).all (fun a =>
      isTypeB env b.uvars ((b.params ++ t.indices.take a).reverse) t.indices[a]! &&
      annB env b.uvars ((b.params ++ t.indices.take a).reverse) t.indices[a]!) &&
    defEqTyLB env b.uvars [] t.type (forallTel (b.params ++ t.indices) (.sort b.level))) &&
  match b.withTypes env with
  | some env₁ => (List.range b.ntypes).all fun j => (b.types[j]!).ctors.all (b.ctorB env₁ j ·)
  | none => false

theorem fieldB_sound {env : VEnv} {Γ : List VExpr} {d : Nat}
    {f : SField} (h : b.fieldB env Γ d f = true) : b.FieldOK env Γ d f := by
  unfold fieldB at h; unfold Spec.SBlock.FieldOK
  split at h
  · rename_i w hc; rw [hc]; exact defEqTyB_sound h
  · rename_i xs k idx hc
    rw [hc]
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨defEqTyB_sound h1, fun e he => annB_sound (h2 e he),
      fun l hl => hasTypeB_sound (h3 l hl), fun e he => ?_⟩
    have h4 := h4 e he
    split at h4
    · rename_i u hu
      refine ⟨u, sortOfInfer_sound hu, fun ls hne => ?_⟩
      simp only [Bool.or_eq_true] at h4
      rcases h4 with hz | hle
      · exact absurd (eval_of_isAlwaysZero' hz ls) hne
      · exact leN_sound hle ls
    · cases h4

theorem ctorB_sound {env : VEnv} {j : Nat} {c : SCtor}
    (h : b.ctorB env j c = true) : b.CtorOK env j c := by
  unfold ctorB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨isTypeB_sound h1, fun i hi => defEqTyB_sound (h2 i hi),
    fun l hl => hasTypeB_sound (h3 l hl), fun a ha => ?_⟩
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := h4 a ha
  refine ⟨hasSortB_sound g1, annB_sound g2, ?_, b.fieldB_sound g4⟩
  simp only [Bool.or_eq_true] at g3
  exact g3.imp id leN_sound

theorem checkWF_sound {env : VEnv} (h : b.checkWF env = true) : b.WF env := by
  unfold checkWF at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hs, hl⟩, hp⟩, ht⟩, hc⟩ := h
  refine ⟨hs, hl, fun i hi => ?_, fun t ht' => ?_, ?_⟩
  · obtain ⟨a, c⟩ := hp i hi; exact ⟨isTypeB_sound a, annB_sound c⟩
  · obtain ⟨hi, hd⟩ := ht t ht'
    exact ⟨fun a ha => ⟨isTypeB_sound (hi a ha).1, annB_sound (hi a ha).2⟩,
      defEqTyLB_sound hd⟩
  · split at hc
    · rename_i env₁ hw
      simp only [List.all_eq_true, List.mem_range] at hc
      exact ⟨env₁, hw, fun j hj c hc' => b.ctorB_sound (hc j hj c hc')⟩
    · cases hc


end Soulgem.Spec.SBlock
