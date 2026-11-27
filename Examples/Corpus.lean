import Examples.Blocks
import Examples.NestedBlocks
import Examples.NestedChain

/-! # `Acc`, mutual `Corpus.Ev`/`Corpus.Od` and `Corpus.B := mk (List (Array B))`, admitted -/

namespace Soulgem.Examples
open Lean4Lean Soulgem Soulgem.Spec

def corpusSteps : List Step :=
  [.plain List_block, .plain Acc_block, .plain Corpus_Ev_block, .plain Array_block,
   .nested Corpus_B_udecl Corpus_B_tblock]

theorem corpus_isSome : (chainN Core.coreEnv [] corpusSteps).isSome = true := by decide +kernel

theorem corpus_admitted :
    Admits Core.coreEnv ((chainN Core.coreEnv [] corpusSteps).get corpus_isSome).1
      ((chainN Core.coreEnv [] corpusSteps).get corpus_isSome).2 :=
  chainN_admits_get .base corpus_isSome

/-- `Corpus.Ev`/`Corpus.Od` is one block; `Corpus.B` has three auxiliaries. -/
theorem corpus_record :
    ((chainN Core.coreEnv [] corpusSteps).get corpus_isSome).2.map (fun r => (r.b.names, r.nuser)) =
      [([`List], 1), ([`Acc], 1), ([`Corpus.Ev, `Corpus.Od], 2), ([`Array], 1),
       ([`Corpus.B, `_nested.List_1, `_nested.Array_2, `_nested.List_3], 1)] := by
  decide +kernel

end Soulgem.Examples
