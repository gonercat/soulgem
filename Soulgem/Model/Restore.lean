import Soulgem.Model.Subst
import Soulgem.Model.TeleSat

/-! # Restoration commutes with interpretation -/

namespace Soulgem
open ConLeche ConLeche.SetTheory Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V]

/-! ## Spines -/

theorem appN_headArgs : ∀ e : VExpr, appN (headArgs e).1 (headArgs e).2 = e
  | .app f a => by
    have := appN_headArgs f
    simp only [headArgs]
    rw [show appN (headArgs f).1 ((headArgs f).2 ++ [a]) = .app
        (appN (headArgs f).1 (headArgs f).2) a
      by simp [appN, List.foldl_append]]
    rw [this]
  | .bvar _ | .sort _ | .const .. | .lam .. | .forallE .. => rfl

theorem headArgs_not_app : ∀ e : VExpr, ∀ f a, (headArgs e).1 ≠ .app f a
  | .app f' _, f, a => by simp only [headArgs]; exact headArgs_not_app f' f a
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lam .., _, _ | .forallE .., _, _ => by
    simp [headArgs]

theorem remap_appN (g : Nat → Nat) (k : Nat) (f : VExpr) :
    ∀ as : List VExpr, remap g (appN f as) k = appN (remap g f k) (as.map (remap g · k))
  | [] => rfl
  | a :: as => by simp only [appN, List.foldl, List.map]; exact remap_appN g k (.app f a) as

theorem headArgs_appN : ∀ (e : VExpr) (as : List VExpr),
    headArgs (appN e as) = ((headArgs e).1, (headArgs e).2 ++ as)
  | e, [] => by simp [appN]
  | e, a :: as => by
    have := headArgs_appN (.app e a) as
    simp only [appN, List.foldl] at this ⊢
    rw [this]; simp [headArgs]

theorem headArgs_appN_of_not_app {h : VExpr} (hh : ∀ f a, h ≠ .app f a) (as : List VExpr) :
    headArgs (appN h as) = (h, as) := by
  rw [headArgs_appN]
  cases h <;> first | (exact absurd rfl (hh _ _)) | simp [headArgs]

theorem headArgs_remap (g : Nat → Nat) (k : Nat) (e : VExpr) :
    headArgs (remap g e k) = (remap g (headArgs e).1 k, (headArgs e).2.map (remap g · k)) := by
  conv => lhs; rw [← appN_headArgs e]
  rw [remap_appN]
  apply headArgs_appN_of_not_app
  intro f a hfa
  have hne := headArgs_not_app e
  generalize hh : (headArgs e).1 = h at hfa hne
  cases h <;> simp [remap] at hfa
  · rename_i i; split at hfa <;> cases hfa
  · exact hne _ _ rfl

theorem range_getD_eq_take {xs : List V} {n : Nat} (h : n ≤ xs.length) :
    (List.range n).map (fun L => xs.getD L pt) = xs.take n := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have hi : i < xs.length := by simp at h1; omega
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

/-! ## The commutation lemma -/

def rename (auxRec : List (Name × Name)) (c : Name) : Name :=
  ((auxRec.find? (·.1 == c)).map (·.2)).getD c

structure RestoreHyp (M M' : CInterp V) (ls : List Nat) (tr : Translated)
    (auxRec : List (Name × Name)) (ns ms : List Name) (us : List VLevel) (n : Nat)
    (Q : List V → Prop) : Prop where
  ns_iff : ∀ c, c ∈ ns ↔ ((tr.aux.find? (·.name == c)).isSome ∨ (tr.auxOfCtor? c).isSome)
  ms_ns : ∀ c ∈ ns, c ∈ ms
  ms_rec : ∀ p ∈ auxRec, p.1 ∈ ms
  rec_ns : ∀ p ∈ auxRec, p.1 ∉ ns
  key_head : ∀ a ∈ tr.aux, ∃ Ic Ils Ds, headArgs a.key = (.const Ic Ils, Ds)
  other : ∀ c, c ∉ ns → M c = M' (rename auxRec c)
  closed : ∀ a ∈ tr.aux, a.key.ClosedN n
  aux : ∀ a ∈ tr.aux, ∀ xs : List V, xs.length = n → Q xs →
    xs.foldl app (M a.name (us.map (·.eval ls))) = interp M' ls a.key xs.reverse
  ctor : ∀ c a, tr.auxOfCtor? c = some a → ∀ Ic Ils Ds, headArgs a.key = (.const Ic Ils, Ds) →
    ∀ xs : List V, xs.length = n → Q xs →
      xs.foldl app (M c (us.map (·.eval ls))) =
        interp M' ls (appN (.const (c.replacePrefix a.name Ic) Ils) Ds) xs.reverse

variable {M M' : CInterp V} {ls : List Nat} {tr : Translated} {auxRec : List (Name × Name)}
  {ns ms : List Name} {us : List VLevel} {n : Nat} {Q : List V → Prop}

theorem rename_of_not_key {c : Name} (h : ∀ p ∈ auxRec, p.1 ≠ c) : rename auxRec c = c := by
  unfold rename
  rw [List.find?_eq_none.mpr fun p hp => by simpa using h p hp]
  rfl

theorem RestoreHyp.interp_free (H : RestoreHyp M M' ls tr auxRec ns ms us n Q) {e : VExpr}
    (he : mentions ms e = false) (ρ : List V) : interp M ls e ρ = interp M' ls e ρ :=
  interp_congr ((constsIn_of_mentions he).mono fun c hc => by
    have hns : c ∉ ns := fun h => hc (H.ms_ns c h)
    have hk : ∀ p ∈ auxRec, p.1 ≠ c := fun p hp hpc => hc (by rw [← hpc]; exact H.ms_rec p hp)
    show M c = M' c
    rw [H.other c hns, rename_of_not_key hk]) ρ

/-! ## What `restoreNode` does -/

section Node
variable (tr : Translated) (auxRec : List (Name × Name)) (n d : Nat)

def NotRec (auxRec : List (Name × Name)) (t : VExpr) : Prop :=
  ∀ c ls, t = .const c ls → auxRec.find? (·.1 == c) = none

theorem notRec_app (f x : VExpr) : NotRec auxRec (.app f x) := fun _ _ h => by cases h

theorem restoreNode_aux {t : VExpr} (hr : NotRec auxRec t) {c : Name} {us' : List VLevel}
    {args : List VExpr} {a : Aux} (hh : headArgs t = (.const c us', args))
    (ha : tr.aux.find? (·.name == c) = some a) :
    tr.restoreNode auxRec n d t = some (appN (place n id d a.key) (args.drop n)) := by
  unfold Translated.restoreNode
  cases t <;> simp only [hh, ha] <;> (try simp only [hr _ _ rfl]) <;> rfl

theorem restoreNode_ctor {t : VExpr} (hr : NotRec auxRec t) {c : Name} {us' : List VLevel}
    {args : List VExpr} {a : Aux} {Ic : Name} {Ils : List VLevel} {Ds : List VExpr}
    (hh : headArgs t = (.const c us', args))
    (ha : tr.aux.find? (·.name == c) = none) (hc : tr.auxOfCtor? c = some a)
    (hk : headArgs (place n id d a.key) = (.const Ic Ils, Ds)) :
    tr.restoreNode auxRec n d t =
      some (appN (.const (c.replacePrefix a.name Ic) Ils) (Ds ++ args.drop n)) := by
  unfold Translated.restoreNode
  cases t <;> simp only [hh, ha, hc] <;> (try simp only [hr _ _ rfl]) <;>
    simp only [bind, Option.bind, hk] <;> rfl

theorem restoreNode_other {t : VExpr} (hr : NotRec auxRec t) {c : Name} {us' : List VLevel}
    {args : List VExpr} (hh : headArgs t = (.const c us', args))
    (ha : tr.aux.find? (·.name == c) = none) (hc : tr.auxOfCtor? c = none) :
    tr.restoreNode auxRec n d t = none := by
  unfold Translated.restoreNode
  cases t <;> simp only [hh, ha, hc] <;> (try simp only [hr _ _ rfl]) <;> rfl

theorem restoreNode_head {t : VExpr} (hr : NotRec auxRec t) {h : VExpr} {args : List VExpr}
    (hh : headArgs t = (h, args)) (hn : ∀ c us', h ≠ .const c us') :
    tr.restoreNode auxRec n d t = none := by
  unfold Translated.restoreNode
  cases t <;> (try simp only [hr _ _ rfl]) <;> simp only [hh] <;>
    (cases h <;> first | rfl | exact absurd rfl (hn _ _))

theorem restoreNode_rec {c r : Name} {ls : List VLevel} {p : Name × Name}
    (hp : auxRec.find? (·.1 == c) = some p) (hr : p.2 = r) :
    tr.restoreNode auxRec n d (.const c ls) = some (.const r ls) := by
  unfold Translated.restoreNode
  simp only [hp, ← hr]
  rfl

end Node

/-! ## The induction -/

theorem closedN_appN_args {h : VExpr} {k : Nat} :
    ∀ {as : List VExpr}, (appN h as).ClosedN k → ∀ a ∈ as, a.ClosedN k
  | [], _, _, ha => by simp at ha
  | b :: as, hc, a, ha => by
    simp only [appN, List.foldl] at hc
    have h' := closedN_appN_args (h := .app h b) hc
    rcases List.mem_cons.mp ha with rfl | ha
    · have : (appN (.app h a) as).ClosedN k := hc
      exact (closedN_appN_head this).2
    · exact h' a ha
where
  closedN_appN_head {h : VExpr} {k : Nat} : ∀ {as : List VExpr}, (appN h as).ClosedN k → h.ClosedN k
    | [], hc => hc
    | b :: as, hc => (closedN_appN_head (h := .app h b) (as := as) hc).1

theorem restoreNode_nonapp {t : VExpr} (ht : ∀ f a, t ≠ .app f a) (hc : ∀ c us, t ≠ .const c us)
    (tr : Translated) (auxRec : List (Name × Name)) (n d : Nat) :
    tr.restoreNode auxRec n d t = none := by
  cases t <;> first | exact absurd rfl (ht _ _) | exact absurd rfl (hc _ _) |
    simp [Translated.restoreNode, headArgs]

/-! ## Spines under interpretation -/

theorem interp_spine (M : CInterp V) (ls : List Nat) (t : VExpr) (ρ : List V) :
    interp M ls t ρ = ((headArgs t).2.map (interp M ls · ρ)).foldl app
        (interp M ls (headArgs t).1 ρ) := by
  conv => lhs; rw [← appN_headArgs t]
  exact interp_appN M ls _ _ _

theorem interp_param_vars (M : CInterp V) (ls : List Nat) {ρ : List V} {d : Nat} (hn : n ≤ d)
    (hd : ρ.length = d) : (vars d 0 n).map (interp M ls · ρ) = ρ.reverse.take n := by
  have := interp_vars M ls (xs := ρ.reverse) (d := d) (L := 0) (n := n) (by simp [hd]) (by omega)
  simpa using this

theorem interp_place_params (M : CInterp V) (ls : List Nat) {ρ : List V} {d : Nat} (hn : n ≤ d)
    (hd : ρ.length = d) {e : VExpr} (hc : e.ClosedN n) :
    interp M ls (place n id d e) ρ = interp M ls e (ρ.reverse.take n).reverse := by
  have := interp_place M ls n id d e ρ.reverse hc (by simp [hd]) (fun L hL => by simp; omega)
  rw [List.reverse_reverse] at this
  rw [this]
  show interp M ls e ((List.range n).map (fun L => ρ.reverse.getD L pt)).reverse = _
  rw [range_getD_eq_take (by rw [List.length_reverse, hd]; exact hn)]

/-! ## The two replacement cases -/

variable {M M' : CInterp V} {ls : List Nat} {tr : Translated} {auxRec : List (Name × Name)}
  {ns ms : List Name} {us : List VLevel} {n : Nat} {Q : List V → Prop}

theorem RestoreHyp.aux_case (H : RestoreHyp M M' ls tr auxRec ns ms us n Q) {t : VExpr} {d : Nat}
    {ρ : List V} (hn : n ≤ d) (hd : ρ.length = d) (hQ : Q (ρ.reverse.take n)) {c : Name}
    {us' : List VLevel} {args : List VExpr} {a : Aux} (hh : headArgs t = (.const c us', args))
    (ha : tr.aux.find? (·.name == c) = some a) (hus : us' = us)
    (htake : args.take n = vars d 0 n) (hrest : ∀ x ∈ args.drop n, mentions ms x = false) :
    interp M' ls (appN (place n id d a.key) (args.drop n)) ρ = interp M ls t ρ := by
  have hmem : a ∈ tr.aux := List.mem_of_find?_eq_some ha
  have hname : a.name = c := by simpa using List.find?_some ha
  have hps : (ρ.reverse.take n).length = n := by simp [hd]; omega
  rw [interp_spine M ls t ρ, hh, interp_appN, interp_place_params M' ls hn hd (H.closed a hmem)]
  conv => rhs; rw [← List.take_append_drop n args]
  rw [List.map_append, List.foldl_append, htake, interp_param_vars M ls hn hd]
  have hc : interp M ls (.const c us') ρ = M a.name (us.map (·.eval ls)) := by
    simp [interp, hname, hus]
  simp only at hc ⊢
  rw [hc, H.aux a hmem _ hps hQ]
  congr 1
  exact List.map_congr_left fun x hx => (H.interp_free (hrest x hx) ρ).symm

theorem closedN_appN_of {k : Nat} : ∀ {f : VExpr} {as : List VExpr}, f.ClosedN k →
    (∀ a ∈ as, a.ClosedN k) → (appN f as).ClosedN k
  | _, [], hf, _ => hf
  | f, a :: as, hf, ha => by
    simp only [appN, List.foldl]
    exact closedN_appN_of (f := .app f a) ⟨hf, ha a (by simp)⟩ fun x hx => ha x (by simp [hx])

theorem RestoreHyp.ctor_case (H : RestoreHyp M M' ls tr auxRec ns ms us n Q) {t : VExpr} {d : Nat}
    {ρ : List V} (hn : n ≤ d) (hd : ρ.length = d) (hQ : Q (ρ.reverse.take n)) {c : Name}
    {us' : List VLevel} {args : List VExpr} {a : Aux} {Ic : Name} {Ils : List VLevel}
    {Ds : List VExpr} (hh : headArgs t = (.const c us', args)) (hc : tr.auxOfCtor? c = some a)
    (hk : headArgs (place n id d a.key) = (.const Ic Ils, Ds)) (hus : us' = us)
    (htake : args.take n = vars d 0 n) (hrest : ∀ x ∈ args.drop n, mentions ms x = false) :
    interp M' ls (appN (.const (c.replacePrefix a.name Ic) Ils) (Ds ++ args.drop n)) ρ =
      interp M ls t ρ := by
  have hmem : a ∈ tr.aux := List.mem_of_find?_eq_some hc
  obtain ⟨Ic0, Ils0, Ds0, hk0⟩ := H.key_head a hmem
  have hkey := appN_headArgs a.key
  rw [hk0] at hkey
  have hpl : headArgs (place n id d a.key) =
      (.const Ic0 Ils0, Ds0.map (remap (fun i => d - 1 - id (n - 1 - i)) · 0)) := by
    unfold place; rw [headArgs_remap, hk0]; rfl
  rw [hpl] at hk
  simp only [Prod.mk.injEq, VExpr.const.injEq] at hk
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
  have hcl : (appN (.const (c.replacePrefix a.name Ic0) Ils0) Ds0).ClosedN n := by
    have := H.closed a hmem
    rw [← hkey] at this
    exact closedN_appN_of trivial (closedN_appN_args this)
  have hps : (ρ.reverse.take n).length = n := by simp [hd]; omega
  have hplace : appN (.const (c.replacePrefix a.name Ic0) Ils0)
      (Ds0.map (remap (fun i => d - 1 - id (n - 1 - i)) · 0)) =
      place n id d (appN (.const (c.replacePrefix a.name Ic0) Ils0) Ds0) := by
    unfold place; rw [remap_appN]; rfl
  rw [show appN (VExpr.const (c.replacePrefix a.name Ic0) Ils0)
      (Ds0.map (remap (fun i => d - 1 - id (n - 1 - i)) · 0) ++ args.drop n) =
      appN (appN (.const (c.replacePrefix a.name Ic0) Ils0)
        (Ds0.map (remap (fun i => d - 1 - id (n - 1 - i)) · 0))) (args.drop n) by
    simp [appN, List.foldl_append]]
  rw [interp_appN M' ls _ (args.drop n), hplace, interp_place_params M' ls hn hd hcl,
    ← H.ctor c a hc Ic0 Ils0 Ds0 hk0 _ hps hQ]
  rw [interp_spine M ls t ρ, hh]
  conv => rhs; rw [← List.take_append_drop n args]
  rw [List.map_append, List.foldl_append, htake, interp_param_vars M ls hn hd]
  simp only [interp, hus]
  congr 1
  exact List.map_congr_left fun x hx => (H.interp_free (hrest x hx) ρ).symm

/-! ## Unfolding `restoreBody` -/

section Unfold
variable (tr : Translated) (auxRec : List (Name × Name)) (n d : Nat)

theorem restoreBody_some {t r : VExpr} (h : tr.restoreNode auxRec n d t = some r) :
    tr.restoreBody auxRec n t d = r := by
  cases t <;> rw [Translated.restoreBody, h] <;> first | rfl | (intro _ _ h'; cases h')

theorem restoreBody_app {f x : VExpr} (h : tr.restoreNode auxRec n d (.app f x) = none) :
    tr.restoreBody auxRec n (.app f x) d =
      .app (tr.restoreBody auxRec n f d) (tr.restoreBody auxRec n x d) := by
  rw [Translated.restoreBody, h]

theorem restoreBody_lam {A b : VExpr} :
    tr.restoreBody auxRec n (.lam A b) d =
      .lam (tr.restoreBody auxRec n A d) (tr.restoreBody auxRec n b (d + 1)) := by
  rw [Translated.restoreBody, restoreNode_nonapp (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)]

theorem restoreBody_forallE {A b : VExpr} :
    tr.restoreBody auxRec n (.forallE A b) d =
      .forallE (tr.restoreBody auxRec n A d) (tr.restoreBody auxRec n b (d + 1)) := by
  rw [Translated.restoreBody, restoreNode_nonapp (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)]

theorem restoreBody_bvar {i : Nat} : tr.restoreBody auxRec n (.bvar i) d = .bvar i := by
  rw [Translated.restoreBody, restoreNode_nonapp (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)]
  all_goals first | rfl | (intro _ _ h; cases h)

theorem restoreBody_sort {u : VLevel} : tr.restoreBody auxRec n (.sort u) d = .sort u := by
  rw [Translated.restoreBody, restoreNode_nonapp (fun _ _ h => by cases h)
      (fun _ _ h => by cases h)]
  all_goals first | rfl | (intro _ _ h; cases h)

theorem restoreBody_const {c : Name} {ls : List VLevel}
    (h : tr.restoreNode auxRec n d (.const c ls) = none) :
    tr.restoreBody auxRec n (.const c ls) d = .const c ls := by
  rw [Translated.restoreBody, h]
  all_goals first | rfl | (intro _ _ h; cases h)

end Unfold

/-! ## Restoration commutes with interpretation -/

theorem find_rec_none {c : Name} (h : ∀ p ∈ auxRec, p.1 ≠ c) : auxRec.find? (·.1 == c) = none :=
  List.find?_eq_none.mpr fun p hp => by simpa using h p hp

structure RestoreNames (tr : Translated) (auxRec : List (Name × Name)) (ns : List Name) : Prop where
  ns_iff : ∀ c, c ∈ ns ↔ ((tr.aux.find? (·.name == c)).isSome ∨ (tr.auxOfCtor? c).isSome)
  rec_ns : ∀ p ∈ auxRec, p.1 ∉ ns
  key_head : ∀ a ∈ tr.aux, ∃ Ic Ils Ds, headArgs a.key = (.const Ic Ils, Ds)

theorem RestoreNames.not_rec (N : RestoreNames tr auxRec ns) {c : Name} (hc : c ∈ ns) :
    auxRec.find? (·.1 == c) = none :=
  find_rec_none fun p hp hpc => N.rec_ns p hp (hpc ▸ hc)

theorem RestoreNames.none_of_not_ns (N : RestoreNames tr auxRec ns) {c : Name} (hc : c ∉ ns) :
    tr.aux.find? (·.name == c) = none ∧ tr.auxOfCtor? c = none := by
  have h := fun hx => hc ((N.ns_iff c).mpr hx)
  constructor
  · cases ha : tr.aux.find? (·.name == c) with
    | none => rfl
    | some _ => exact absurd (Or.inl (by simp [ha])) h
  · cases hct : tr.auxOfCtor? c with
    | none => rfl
    | some _ => exact absurd (Or.inr (by simp [hct])) h

theorem RestoreNames.place_head (N : RestoreNames tr auxRec ns) {a : Aux} (ha : a ∈ tr.aux)
    (n d : Nat) : ∃ Ic Ils Ds, headArgs a.key = (.const Ic Ils, Ds) ∧
      headArgs (place n id d a.key) =
        (.const Ic Ils, Ds.map (remap (fun i => d - 1 - id (n - 1 - i)) · 0)) := by
  obtain ⟨Ic, Ils, Ds, hk0⟩ := N.key_head a ha
  exact ⟨Ic, Ils, Ds, hk0, by unfold place; rw [headArgs_remap, hk0]; rfl⟩

theorem RestoreNames.induction (N : RestoreNames tr auxRec ns) {us : List VLevel} {n : Nat}
    (C : Nat → VExpr → VExpr → Prop)
    (bvar : ∀ d i, n ≤ d → C d (.bvar i) (.bvar i))
    (sort : ∀ d u, n ≤ d → C d (.sort u) (.sort u))
    (aux : ∀ d t c us' args a, n ≤ d → headArgs t = (.const c us', args) →
      tr.aux.find? (·.name == c) = some a → us' = us → args.take n = vars d 0 n →
      (∀ x ∈ args.drop n, mentions ms x = false) →
      C d t (appN (place n id d a.key) (args.drop n)))
    (ctor : ∀ d t c us' args a Ic Ils Ds, n ≤ d → headArgs t = (.const c us', args) →
      tr.auxOfCtor? c = some a → headArgs (place n id d a.key) = (.const Ic Ils, Ds) →
      us' = us → args.take n = vars d 0 n → (∀ x ∈ args.drop n, mentions ms x = false) →
      C d t (appN (.const (c.replacePrefix a.name Ic) Ils) (Ds ++ args.drop n)))
    (rec : ∀ d c us' p, n ≤ d → c ∉ ns → auxRec.find? (·.1 == c) = some p →
      C d (.const c us') (.const p.2 us'))
    (other : ∀ d c us', n ≤ d → c ∉ ns → auxRec.find? (·.1 == c) = none →
      C d (.const c us') (.const c us'))
    (lam : ∀ d A A' b b', n ≤ d → C d A A' → C (d + 1) b b' → C d (.lam A b) (.lam A' b'))
    (pi : ∀ d A A' b b', n ≤ d → C d A A' → C (d + 1) b b' →
      C d (.forallE A b) (.forallE A' b'))
    (app : ∀ d f f' x x', n ≤ d → C d f f' → C d x x' → C d (.app f x) (.app f' x')) :
    ∀ (e : VExpr) {d : Nat}, n ≤ d → restoreSafe ns ms us n e d = true →
      C d e (tr.restoreBody auxRec n e d)
  | .bvar i, d, hn, _ => by rw [restoreBody_bvar]; exact bvar d i hn
  | .sort u, d, hn, _ => by rw [restoreBody_sort]; exact sort d u hn
  | .const c us', d, hn, hs => by
    by_cases hc : c ∈ ns
    · have hcon : ns.contains c = true := List.contains_iff_mem.mpr hc
      simp only [restoreSafe, hcon, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hs
      obtain ⟨hus, rfl⟩ := hs
      have hr : NotRec auxRec (.const c us') := fun c' _ he => by cases he; exact N.not_rec hc
      have hh : headArgs (.const c us') = (.const c us', []) := rfl
      have htake : ([] : List VExpr).take 0 = vars d 0 0 := by simp [vars]
      cases ha : tr.aux.find? (·.name == c) with
      | some a =>
        rw [restoreBody_some tr auxRec 0 d (restoreNode_aux tr auxRec 0 d hr hh ha)]
        exact aux d _ c us' [] a hn hh ha hus htake (by simp)
      | none =>
        have hct : (tr.auxOfCtor? c).isSome := by
          rcases (N.ns_iff c).mp hc with h | h
          · simp [ha] at h
          · exact h
        obtain ⟨a, hct⟩ := Option.isSome_iff_exists.mp hct
        obtain ⟨Ic, Ils, _, -, hk⟩ := N.place_head (List.mem_of_find?_eq_some hct) 0 d
        rw [restoreBody_some tr auxRec 0 d (restoreNode_ctor tr auxRec 0 d hr hh ha hct hk)]
        exact ctor d _ c us' [] a Ic Ils _ hn hh hct hk hus htake (by simp)
    · cases hp : auxRec.find? (·.1 == c) with
      | some p =>
        rw [restoreBody_some tr auxRec n d (restoreNode_rec tr auxRec n d hp rfl)]
        exact rec d c us' p hn hc hp
      | none =>
        have hr : NotRec auxRec (.const c us') := fun c' _ he => by cases he; exact hp
        obtain ⟨ha, hct⟩ := N.none_of_not_ns hc
        rw [restoreBody_const tr auxRec n d (restoreNode_other tr auxRec n d hr rfl ha hct)]
        exact other d c us' hn hc hp
  | .lam A b, d, hn, hs => by
    simp only [restoreSafe, Bool.and_eq_true] at hs
    rw [restoreBody_lam]
    exact lam d _ _ _ _ hn (N.induction C bvar sort aux ctor rec other lam pi app A hn hs.1)
      (N.induction C bvar sort aux ctor rec other lam pi app b (by omega) hs.2)
  | .forallE A b, d, hn, hs => by
    simp only [restoreSafe, Bool.and_eq_true] at hs
    rw [restoreBody_forallE]
    exact pi d _ _ _ _ hn (N.induction C bvar sort aux ctor rec other lam pi app A hn hs.1)
      (N.induction C bvar sort aux ctor rec other lam pi app b (by omega) hs.2)
  | .app f x, d, hn, hs => by
    have hr := notRec_app (auxRec := auxRec) f x
    have hstruct : restoreSafe ns ms us n f d = true → restoreSafe ns ms us n x d = true →
        tr.restoreNode auxRec n d (.app f x) = none →
        C d (.app f x) (tr.restoreBody auxRec n (.app f x) d) := fun hf hx hnone => by
      rw [restoreBody_app tr auxRec n d hnone]
      exact app d _ _ _ _ hn (N.induction C bvar sort aux ctor rec other lam pi app f hn hf)
        (N.induction C bvar sort aux ctor rec other lam pi app x hn hx)
    rcases hh : headArgs (.app f x) with ⟨h, args⟩
    rw [restoreSafe, hh] at hs
    cases h with
    | const c us' =>
      by_cases hc : c ∈ ns
      · have hcon : ns.contains c = true := List.contains_iff_mem.mpr hc
        simp only [hcon, ite_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          Bool.not_eq_true'] at hs
        obtain ⟨⟨⟨hus, -⟩, htake⟩, hrest⟩ := hs
        cases ha : tr.aux.find? (·.name == c) with
        | some a =>
          rw [restoreBody_some tr auxRec n d (restoreNode_aux tr auxRec n d hr hh ha)]
          exact aux d _ c us' args a hn hh ha hus htake hrest
        | none =>
          have hct : (tr.auxOfCtor? c).isSome := by
            rcases (N.ns_iff c).mp hc with h | h
            · simp [ha] at h
            · exact h
          obtain ⟨a, hct⟩ := Option.isSome_iff_exists.mp hct
          obtain ⟨Ic, Ils, _, -, hk⟩ := N.place_head (List.mem_of_find?_eq_some hct) n d
          rw [restoreBody_some tr auxRec n d (restoreNode_ctor tr auxRec n d hr hh ha hct hk)]
          exact ctor d _ c us' args a Ic Ils _ hn hh hct hk hus htake hrest
      · have hcon : ns.contains c = false := by
          cases h : ns.contains c with
          | false => rfl
          | true => exact absurd (List.contains_iff_mem.mp h) hc
        simp only [hcon, Bool.false_eq_true, ite_false, Bool.and_eq_true] at hs
        obtain ⟨ha, hct⟩ := N.none_of_not_ns hc
        exact hstruct hs.1 hs.2 (restoreNode_other tr auxRec n d hr hh ha hct)
    | bvar | sort | app | lam | forallE =>
      simp only [Bool.and_eq_true] at hs
      exact hstruct hs.1 hs.2 (restoreNode_head tr auxRec n d hr hh (fun _ _ h => by cases h))

theorem RestoreHyp.names (H : RestoreHyp M M' ls tr auxRec ns ms us n Q) :
    RestoreNames tr auxRec ns := ⟨H.ns_iff, H.rec_ns, H.key_head⟩

omit [SetTheory V] in
theorem take_reverse_cons {ρ : List V} {x : V} {n : Nat} (hn : n ≤ ρ.length) :
    (x :: ρ).reverse.take n = ρ.reverse.take n := by
  simp only [List.reverse_cons]
  exact List.take_append_of_le_length (by simp; omega)

theorem RestoreHyp.interp_restoreBody (H : RestoreHyp M M' ls tr auxRec ns ms us n Q)
    (e : VExpr) {d : Nat} {ρ : List V} (hn : n ≤ d) (hd : ρ.length = d)
    (hQ : Q (ρ.reverse.take n)) (hs : restoreSafe ns ms us n e d = true) :
    interp M' ls (tr.restoreBody auxRec n e d) ρ = interp M ls e ρ := by
  refine H.names.induction (us := us) (ms := ms)
    (fun d e e' => ∀ ρ : List V, ρ.length = d → Q (ρ.reverse.take n) →
      interp M' ls e' ρ = interp M ls e ρ)
    (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ hn hh ha hus htake hrest ρ hd hQ =>
      H.aux_case hn hd hQ hh ha hus htake hrest)
    (fun _ _ _ _ _ _ _ _ _ hn hh hct hk hus htake hrest ρ hd hQ =>
      H.ctor_case hn hd hQ hh hct hk hus htake hrest)
    (fun _ c _ p _ hc hp ρ _ _ => by
      simp only [interp]
      rw [H.other c hc]
      unfold rename; rw [hp]; rfl)
    (fun _ c _ _ hc hp ρ _ _ => by
      simp only [interp]
      rw [H.other c hc, rename_of_not_key fun p hpm hpc => by
        have := List.find?_eq_none.mp hp p hpm; simp [hpc] at this])
    (fun _ _ _ _ _ hn hA hb ρ hd hQ => by
      simp only [interp]
      rw [hA ρ hd hQ]
      congr 1; funext x
      exact hb (x :: ρ) (by simp [hd]) (by rw [take_reverse_cons (by omega)]; exact hQ))
    (fun _ _ _ _ _ hn hA hb ρ hd hQ => by
      simp only [interp]
      rw [hA ρ hd hQ]
      congr 1; funext x
      exact hb (x :: ρ) (by simp [hd]) (by rw [take_reverse_cons (by omega)]; exact hQ))
    (fun _ _ _ _ _ _ hf hx ρ hd hQ => by
      simp only [interp]
      rw [hf ρ hd hQ, hx ρ hd hQ])
    e hn hs ρ hd hQ

end Soulgem
