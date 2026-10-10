import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerRawCorrectness
import Holant.Complexity.FixedGadgetSubstitution.Adjoin

/-! An unbounded unary-indexed positive-chain query, including the actual
fixed macro expansion back to the original dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerValidated
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution RawClosedNetwork
namespace O
export GlobalCloseCompletionComplementQ4ChainCompilerOccurrence (templates raw raw_eq_replace rawComputes inputEncoding)
end O
namespace R
export GlobalCloseCompletionComplementQ4ChainCompilerRecords (valid explicitTemplate)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} (a : ℕ→ℕ) (g : Template) (hg : g.WellFormed s b a)
variable (hfour : g.boundary=4) (edge : Fin b)
abbrev macroArity:=sourceArity (Adjoin.templates s a g)
abbrev SourceInput:=FixedGadgetSubstitution.Compiler.Input (s+1) b (macroArity (s:=s) a g)
abbrev sourceEncoding:=validatedEncoding (s+1) b (macroArity (s:=s) a g)
abbrev Input:=SourceInput (s:=s) (b:=b) a g × ℕ
abbrev inputEncoding:=pairEncoding (sourceEncoding (s:=s) (b:=b) a g) UnaryBinary.unaryEncoding

include hfour in
theorem chain_hypotheses (k : ℕ) : ∀i<s+1,
    (O.templates (macroArity (s:=s) a g) s s edge.val k i).WellFormed (s+1) b (macroArity (s:=s) a g) ∧
    (O.templates (macroArity (s:=s) a g) s s edge.val k i).boundary=macroArity (s:=s) a g i := by
  intro i hi
  by_cases h : i=s
  · subst i
    simp only [O.templates,ite_true]
    refine ⟨R.valid (macroArity (s:=s) a g) (⟨s,Nat.lt_succ_self s⟩ : Fin (s+1))
      ((Adjoin.new_boundary g).trans hfour) edge k,?_⟩
    exact hfour.symm.trans (Adjoin.new_boundary g).symm
  · simp only [O.templates,h,ite_false]
    exact ⟨identityTemplate_wellFormed (macroArity (s:=s) a g) (⟨i,hi⟩ : Fin (s+1)),rfl⟩

def intermediate (x : Input (s:=s) (b:=b) a g) : SourceInput (s:=s) (b:=b) a g:=
  ⟨O.raw (s+1) b (macroArity (s:=s) a g) s s edge.val (x.2,x.1),by
    rw [O.raw_eq_replace]
    exact replace_wellFormed _ _ x.1.property (chain_hypotheses a g hfour edge x.2)⟩

def intermediateComputes : Computes (inputEncoding (s:=s) (b:=b) a g)
    (sourceEncoding (s:=s) (b:=b) a g) (intermediate a g hfour edge) := by
  let swap:=pairComputes
    (Wiring.secondComputes (sourceEncoding (s:=s) (b:=b) a g) UnaryBinary.unaryEncoding)
    (Wiring.firstComputes (sourceEncoding (s:=s) (b:=b) a g) UnaryBinary.unaryEncoding)
  exact recode (swap.andThen (O.rawComputes (s+1) b (macroArity (s:=s) a g) s s edge.val))
    id (fun _=>rfl) (fun _=>rfl)

include hg in
theorem fixed_hypotheses : ∀i<s+1,(Adjoin.templates s a g i).WellFormed s b a ∧
    (Adjoin.templates s a g i).boundary=macroArity (s:=s) a g i:=
  fun i hi=>⟨Adjoin.wellFormed g hg i hi,rfl⟩

def query (x : Input (s:=s) (b:=b) a g) : FixedGadgetSubstitution.Compiler.Input s b a:=
  FixedGadgetSubstitution.Compiler.value (s+1) b (macroArity (s:=s) a g)
    (Adjoin.templates s a g) s a (fixed_hypotheses a g hg) (intermediate a g hfour edge x)

/-- The query executes on every unary index, with no externally supplied bound. -/
def queryComputes : Computes (inputEncoding (s:=s) (b:=b) a g) (validatedEncoding s b a)
    (query a g hg hfour edge):=
  (intermediateComputes a g hfour edge).andThen
    (FixedGadgetSubstitution.Compiler.computes (s+1) b (macroArity (s:=s) a g)
      (Adjoin.templates s a g) s a (fixed_hypotheses a g hg))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerValidated
end
