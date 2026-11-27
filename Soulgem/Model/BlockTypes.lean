import Soulgem.Model.BlockRec
import Soulgem.Model.EnvExt
import Soulgem.Model.Subst

/-! # The block's types in the model -/

namespace Soulgem.BlockModel
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem

universe u
variable {V : Type u} [SetTheory V]

theorem forallTel_append : ∀ (As Bs : List VExpr) (R : VExpr),
    Spec.forallTel (As ++ Bs) R = Spec.forallTel As (Spec.forallTel Bs R)
  | [], _, _ => rfl
  | A :: As, Bs, R => by simp [Spec.forallTel, forallTel_append As Bs R]

theorem Ext.append {M : CInterp V} {ls : List Nat} : ∀ {As Bs : List VExpr} {ρ xs ys : List V},
    Ext M ls As ρ xs → Ext M ls Bs (xs.reverse ++ ρ) ys → Ext M ls (As ++ Bs) ρ (xs ++ ys)
  | [], _, _, _, _, .nil, h => by simpa using h
  | _ :: _, _, _, _, _, .cons hx hxs, h => .cons hx (Ext.append hxs (by simpa using h))

theorem Ext.split {M : CInterp V} {ls : List Nat} : ∀ {As Bs : List VExpr} {ρ zs : List V},
    Ext M ls (As ++ Bs) ρ zs →
    Ext M ls As ρ (zs.take As.length) ∧ Ext M ls Bs ((zs.take As.length).reverse ++ ρ)
        (zs.drop As.length)
  | [], _, _, _, h => ⟨.nil, by simpa using h⟩
  | _ :: _, _, _, _, .cons hx hxs => by
    obtain ⟨h1, h2⟩ := Ext.split hxs
    exact ⟨.cons hx h1, by simpa using h2⟩

def findName : List Name → Name → Nat
  | [], _ => 0
  | n :: ns, c => if n = c then 0 else findName ns c + 1

theorem findName_lt_of_mem : ∀ {ns : List Name} {c : Name}, c ∈ ns → findName ns c < ns.length
  | [], _, h => absurd h (by simp)
  | n :: ns, c, h => by
    by_cases e : n = c
    · simp [findName, e]
    · simp only [findName, ite_eq_right e, List.length_cons]
      have := findName_lt_of_mem ((List.mem_cons.mp h).resolve_left fun h' => e h'.symm)
      omega

theorem findName_getElem : ∀ {ns : List Name}, ns.Nodup → ∀ j (hj : j < ns.length),
    findName ns ns[j] = j
  | n :: ns, hnd, 0, _ => by simp [findName]
  | n :: ns, hnd, j + 1, hj => by
    have hne : n ≠ (n :: ns)[j + 1] := by
      intro h; exact (List.nodup_cons.mp hnd).1 (h ▸ List.getElem_mem (by simpa using hj))
    simp only [findName, ite_eq_right hne]
    simpa using findName_getElem (List.nodup_cons.mp hnd).2 j (by simpa using hj)

theorem findName_not_mem : ∀ {ns : List Name} {c : Name}, c ∉ ns → findName ns c = ns.length
  | [], _, _ => rfl
  | n :: ns, c, h => by
    have hne : n ≠ c := fun e => h (e ▸ .head _)
    simp only [findName, ite_eq_right hne, List.length_cons]
    rw [findName_not_mem fun hc => h (.tail _ hc)]

variable (M : CInterp V) (b : SBlock) (C : List Nat → List V → Nat → V)

noncomputable def former (j : Nat) (ls : List Nat) : V :=
  Soulgem.lamTel M ls b.params (fun ρp =>
    Soulgem.lamTel M ls (b.types[j]!).indices
      (fun ρ => app (C ls ρp j) (mkTower (ρ.take (nidx b j)).reverse)) ρp) []

noncomputable def M₁ : CInterp V := fun c ls =>
  if findName b.names c < b.ntypes then former M b C (findName b.names c) ls else M c ls

def TupleFn (M : CInterp V) (b : SBlock) (C : List Nat → List V → Nat → V) : Prop :=
  ∀ ls ρp, InTupleSpace (lev ls b) b.ntypes (Is M ls b ρp) (C ls ρp)

theorem carrier_tupleFn : TupleFn M b fun ls ρp => carrier M ls b ρp := fun _ _ => carrier_mem

variable {M b C}

theorem names_length : b.names.length = b.ntypes := by simp [SBlock.names, SBlock.ntypes]

theorem M₁_type (hnd : b.names.Nodup) {j : Nat} (hj : j < b.ntypes) (ls : List Nat) :
    M₁ M b C (b.types[j]'hj).name ls = former M b C j ls := by
  have e : findName b.names (b.types[j]'hj).name = j := by
    have := findName_getElem hnd j (by rw [names_length]; exact hj)
    simp only [SBlock.names, List.getElem_map] at this
    exact this
  simp only [M₁, e, ite_eq_left hj]

theorem M₁_other {c : Name} (hc : c ∉ b.names) : M₁ M b C c = M c := by
  funext ls
  have : ¬ findName b.names c < b.ntypes := by
    rw [findName_not_mem hc, names_length]; exact Nat.lt_irrefl _
  simp only [M₁, ite_eq_right this]

theorem interp_sort (ls : List Nat) (l : VLevel) (ρ : List V) :
    interp M ls (.sort l) ρ = univ (l.eval ls) := rfl

theorem former_mem (hC : TupleFn M b C) {env : VEnv} (hM : IsModel M env) {j : Nat}
    (hj : j < b.ntypes)
    (hT : DefEqTy env b.uvars [] (b.types[j]'hj).type
      (Spec.forallTel (b.params ++ (b.types[j]'hj).indices) (.sort b.level)))
    (ls : List Nat) :
    former M b C j ls ∈ˢ interp M ls (b.types[j]'hj).type [] := by
  obtain ⟨_, hT⟩ := hT
  rw [(hM.sound hT ls [] trivial).1, forallTel_append, interp_forallTel]
  have e : (b.types[j]!) = b.types[j]'hj := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show j < b.types.length from hj)]
    rfl
  unfold former; rw [e]
  refine lamTel_mem_piTel fun ps _ => ?_
  rw [interp_forallTel]
  refine lamTel_mem_piTel fun is his => ?_
  have hl : is.length = nidx b j := by rw [Ext.length_eq M ls his, nidx, e]
  have htake : ((is.reverse ++ (ps.reverse ++ [])).take (nidx b j)).reverse = is := by
    rw [List.take_append_of_le_length (by simp [hl]), List.take_of_length_le (by simp [hl])]; simp
  rw [htake, interp_sort]
  refine famSpace_app (hC ls _ j hj) ?_
  unfold Is; rw [e]; simpa using mkTower_mem_extSet M ls his

def typeConsts (b : SBlock) : List (Name × VConstant) :=
  b.types.map fun t => (t.name, { uvars := b.uvars, type := t.type })

theorem withTypes_eq (env : VEnv) : b.withTypes env = addFold env (typeConsts b) := by
  simp only [SBlock.withTypes, addFold, typeConsts, List.foldlM_map]

theorem mem_typeConsts {x : Name × VConstant} (hx : x ∈ typeConsts b) :
    ∃ j, ∃ hj : j < b.ntypes, x = ((b.types[j]'hj).name,
        { uvars := b.uvars, type := (b.types[j]'hj).type }) := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
  exact ⟨j, hj, rfl⟩

theorem model_withTypes (hC : TupleFn M b C) {env env₁ : VEnv} (hM : IsModel M env)
    (hG : Good env)
    (hwt : b.withTypes env = some env₁) (hnd : b.names.Nodup)
    (hT : ∀ j (hj : j < b.ntypes), DefEqTy env b.uvars [] (b.types[j]'hj).type
      (Spec.forallTel (b.params ++ (b.types[j]'hj).indices) (.sort b.level))) :
    IsModel (M₁ M b C) env₁ ∧ Good env₁ := by
  rw [withTypes_eq] at hwt
  obtain ⟨hfr, _, hle, _, _, _⟩ := addFold_spec hwt
  have hnot : ∀ c, Dom env c → c ∉ b.names := by
    intro c hc hm
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    exact hc (hfr (t.name, _) (List.mem_map.mpr ⟨t, ht, rfl⟩))
  have hagree : ∀ c, Dom env c → M₁ M b C c = M c := fun c hc => M₁_other (hnot c hc)
  have htyp : ∀ j (hj : j < b.ntypes), (b.types[j]'hj).type.ClosedN ∧
      ConstsIn (Dom env) (b.types[j]'hj).type := by
    intro j hj
    obtain ⟨_, h⟩ := hT j hj
    exact ⟨(h.closedN' hG.1 trivial).1, (IsDefEq.constsIn hG.2 h nofun).1⟩
  refine ⟨hM.addFold hG hwt hagree fun x hx ls _ ρ => ?_, hG.addFold hwt fun x hx => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := mem_typeConsts hx
    simp only
    rw [M₁_type hnd hj, interp_congr ((htyp j hj).2.mono fun c hc => hagree c hc),
      interp_closed M ls (htyp j hj).1]
    exact former_mem hC hM hj (hT j hj) ls
  · obtain ⟨j, hj, rfl⟩ := mem_typeConsts hx
    exact ⟨(htyp j hj).1, (htyp j hj).2.mono fun _ => Dom.mono hle⟩

end Soulgem.BlockModel
