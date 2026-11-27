import Examples.Blocks
import Examples.NestedBlocks
import Examples.NestedChain

/-! # The rose tree `Corpus.T := node (List T)`, admitted by `Admits.nested` -/

namespace Soulgem.Examples
open Lean4Lean Soulgem Soulgem.Spec

def roseSteps : List Step := [.plain List_block, .nested Corpus_T_udecl Corpus_T_tblock]

theorem rose_isSome : (chainN Core.coreEnv [] roseSteps).isSome = true := by decide +kernel

theorem rose_admitted :
    Admits Core.coreEnv ((chainN Core.coreEnv [] roseSteps).get rose_isSome).1
      ((chainN Core.coreEnv [] roseSteps).get rose_isSome).2 :=
  chainN_admits_get .base rose_isSome

/-- `Corpus.T`'s record: one user type and the auxiliary `List Corpus.T`. -/
theorem rose_record :
    ((chainN Core.coreEnv [] roseSteps).get rose_isSome).2.map (fun r => (r.b.names, r.nuser)) =
      [([`List], 1), ([`Corpus.T, `_nested.List_1], 1)] := by
  decide +kernel

end Soulgem.Examples
