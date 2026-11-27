# soulgem: Lean 4 Consistency Project

soulgem is a formal specification of Lean 4's inductive types and structure η with a consistency and soundness proof.
This shows that every environment admitted by that specification has a model in any `V` with a `ConLeche.SetTheory V`
instance: ZF-style axioms with replacement over Lean functions and an ω-chain of Grothendieck universes. An instance
exists given ω + 1 inaccessible cardinals.

This project builds off of lean4lean and con-leche.

Currently soulgem is based on Lean v4.35.0-rc3.

## Main theorems

Both theorems are in `namespace Soulgem.Nested`.

```lean
theorem Core.consistency_nested (V : Type u) [SetTheory V] {env : VEnv} {rec : List RBlock}
    (H : Admits Core.coreEnv env rec) (U : Nat) : ¬ ∃ e, env.HasType U [] e VExpr.false
```

Consistency - Spec doesn't admit any environment over the core environment that has a closed term of type
`∀ p : Prop, p`.
`Soulgem/Model/Admits.lean`

```lean
theorem Core.sound_standard (V : Type u) [SetTheory V] {env : VEnv} {rec : List RBlock}
    (H : Admits Core.coreEnv env rec) {r : RBlock} (hr : r ∈ rec) (hb : r.b = natBlock)
    (hn : 0 < r.nuser) :
    ∃ M : CInterp V, IsModel M env ∧
      (∀ {U e p}, env.HasType U [] e p → ∀ ls, ∃ x, x ∈ˢ interp M ls p []) ∧
      StdNat (M `Nat []) (M `Nat.zero []) (M `Nat.succ []) ∧
      (∀ {U e s t}, env.HasType U [] s (.const `Nat []) → env.HasType U [] t (.const `Nat []) →
        env.HasType U [] e (eqNat s t) → interp M [] s [] = interp M [] t [])
```

Soundness - every admitted environment has a model in which every derivable closed proposition is inhabited. If
it has the standard Nat block, Nat is the standard natural numbers in that model, so there can be no proof of
1 = 0 (`Core.not_succ_zero_eq_zero`).
`Soulgem/Standard.lean`

Collapsed function spaces - propositions are subsets of `{pt}` and functions that return `pt` everywhere collapse to
`pt`, giving untyped total interpretation `interp M ls : VExpr → List V → V` where impredicative Prop, β, η, and
proof irrelevance hold directly. The proof therefore doesn't need unique typing or normalization.

## Spec

- Base environment: `Eq`, `Iff`, `Nonempty`, `Quot`, standard axioms `propext`, `Classical.choice`, `Quot.sound`.
- Terms - lean4lean's `VExpr`: bound variables, sorts, constants with universe levels, application, `fun`, `∀`.
- Judgment: congruence, conversion, β, function η, proof irrelevance, the environment's declared definitional
  equations.
- Extension steps: `def`, `opaque`, a mutual inductive block with recursors and ι rules, structure η, and nested
  inductives through the auxiliary-type translation.
- New axioms, `let`, quotients beyond the base environment, and unsafe and partial declarations are not covered.

Diverges from the v4.35.0-rc3 kernel:

- Primitive projections are not in `VExpr`, structure η is expressed via recursor applications (`projV`) or named
  projection definitions (`etaProj`).
- Structure/unit η: Spec gives η to a single-type, non-recursive, large-eliminating structure whose level is
  never zero or whose fields don't depend on earlier fields. The kernel gives it to every non-recursive
  single-constructor type without indices, including mutual ones.
- Nesting goes only through inductives added by Spec's own steps. The kernel does also nest through base-environment
  inductives.
- When a universe level object is shared, rc3's `update_max` keeps `max u u` in a nested inductive's recursor type.
  Spec simplifies it to `u`.
- Spec has no K-like reduction rule. Its declarative judgment derives K-like equations from proof irrelevance and ι,
  including some the kernel's checker refuses (`Checks/KDerive.lean`).
- Native `Nat` / `String` literals and arithmetic reduction are not in `VExpr`.
- Spec's admission conditions hold up to definitional equality, so it admits some declarations rc3 refuses for
  syntactic reasons (`Checks/NPBeta.lean`).

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain is pinned to `leanprover/lean4:v4.35.0-rc3`.

```
lake build
lake build Checks # axiom check and rc3 kernel probes
lake build Examples # admitted examples
```

`lake build` is zero-dependency.

## Layout

```
Soulgem/Spec/       specification
Soulgem/Model/      set model of each extension step
Soulgem/            core logic, collapse model, soundness and Nat witness
Checks/             axiom check and rc3 kernel probes
Examples/           admitted examples: nested rose tree, Prod with η, Acc, mutual Ev/Od, List (Array B)
ConLeche/           con-leche's set theory and set-model library
vendor/lean4lean/   lean4lean's VExpr, VLevel and typing judgment
vendor/batteries/   batteries
```

## Future work

Closing Spec gaps, checking Init and Mathlib, verifying kernel.

## Contributions

soulgem is implemented by Claude. Thanks to con-leche, lean4lean, and batteries for the groundwork soulgem builds on.

| Path | Upstream | Commit |
|---|---|---|
| ConLeche/ | [leanprover/con-leche](https://github.com/leanprover/con-leche) | 65e74db |
| vendor/lean4lean/ | [digama0/lean4lean](https://github.com/digama0/lean4lean) | b73a4e7 |
| vendor/batteries/ | [leanprover-community/batteries](https://github.com/leanprover-community/batteries) | 66e46918 |