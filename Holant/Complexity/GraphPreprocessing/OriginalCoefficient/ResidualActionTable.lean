import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextWordTableRun
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionRow
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionTable

/-! Complete conditioned original-ID action tables. The original raw graph
and selected original cut are the only data input; the actual graph scanner
allocates the vertex counter. Every row retains the same cut word. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionTable
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}
def size (x : ResidualContext.Input s b arity) := (ResidualContext.source x).val.vertices.length
noncomputable def sourceComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.encoding s b arity) RawClosedNetwork.encoding (fun x => (ResidualContext.source x).val) :=
  recode (Wiring.firstComputes RawClosedNetwork.encoding encodingNatBool)
    (fun x => ((ResidualContext.source x).val,(ResidualContext.edge x).val)) (fun _ => rfl) (fun _ => rfl)
noncomputable def recordsComputes :
    Computes RawClosedNetwork.encoding (pairEncoding RawClosedNetwork.encoding (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))
      (fun r => (r,r.vertices.length,r.edges.length)) :=
  recode CountsPackage.computes id (fun _ => rfl) (fun _ => rfl)
noncomputable def countComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.encoding s b arity) UnaryBinary.unaryEncoding size :=
  (((sourceComputes s b arity).andThen recordsComputes).andThen
    (Wiring.secondComputes RawClosedNetwork.encoding (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))).andThen
      (Wiring.firstComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
abbrev countMachine := ((Wiring.firstMachine.compose CountsPackage.machine).compose secondMachine).compose Wiring.firstMachine
@[simp] theorem count_machine (s b : ℕ) (arity : ℕ → ℕ) : (countComputes s b arity).machine=countMachine := rfl

def value (a z : Bool) (x : ResidualContext.Input s b arity) := ContextWordTable.rows size (ResidualActionRow.value a z) x
abbrev packageMachine := pairMachine identityMachine (pairMachine countMachine (Constant.machine []))
abbrev machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) := packageMachine.compose (ParentTableLoop.machine (ResidualActionRow.machine a z s b arity))
noncomputable def computes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.encoding s b arity) (framedListEncoding Frame.wordEncoding) (value a z) :=
  ContextWordTable.computes ResidualContext.vertex_bound (countComputes s b arity) (ResidualActionRow.computes a z s b arity)
@[simp] theorem computes_machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : (computes a z s b arity).machine=machine a z s b arity := rfl
theorem inFP (a z : Bool) : InFP (ResidualContext.encoding s b arity) (framedListEncoding Frame.wordEncoding) (value a z) := (computes a z s b arity).inFP
@[simp] theorem value_length (a z : Bool) (x : ResidualContext.Input s b arity) : (value a z x).length=(ResidualContext.source x).val.vertices.length := by simp [value,size]
theorem get_row (a z : Bool) (x : ResidualContext.Input s b arity) (v : Fin (ResidualContext.source x).val.vertices.length) :
    (value a z x)[v.val]'(by simpa using v.isLt)=ResidualActionRow.value a z ⟨x,v⟩ := by simp [value,ContextWordTable.rows]

noncomputable def timePolynomial (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (computes a z s b arity).time.comp (3*(Polynomial.X+1))
noncomputable def timed (a z : Bool) (x : ResidualContext.Input s b arity) :
    TM2OutputsInTime (machine a z s b arity).computer ((ResidualContext.encoding s b arity).encode x)
      (some (Traversal.tableBits (value a z x)))
      ((timePolynomial a z s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x).val).length) where
  steps := ((computes a z s b arity).outputs x).steps
  evals_in_steps := ((computes a z s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (computes a z s b arity).time (ResidualContext.encoded_length x)
    exact le_trans ((computes a z s b arity).outputs x).steps_le_m (by simpa [timePolynomial] using h)
noncomputable def primitivePolynomial (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial a z s b arity*Polynomial.C (machine a z s b arity).primitiveBudget
theorem primitive_bound (a z : Bool) (x : ResidualContext.Input s b arity) :
    primitiveCost (machine a z s b arity) (timed a z x).steps
      (some (initList (machine a z s b arity).computer ((ResidualContext.encoding s b arity).encode x))) ≤
      (primitivePolynomial a z s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x).val).length := by
  have h := Nat.mul_le_mul_right (machine a z s b arity).primitiveBudget (timed a z x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

theorem output_length (a z : Bool) (x : ResidualContext.Input s b arity) :
    let N := (RawClosedNetwork.encoding.encode (ResidualContext.source x).val).length
    let C := lengthBound s b arity
    (Traversal.tableBits (value a z x)).length≤N*(2*(8*C+6+N*(4*C+N+6))+2)+1 := by
  dsimp only
  have hb := RawActionTable.list_length (value a z x) (8*lengthBound s b arity+6+(RawClosedNetwork.encoding.encode (ResidualContext.source x).val).length*
      (4*lengthBound s b arity+(RawClosedNetwork.encoding.encode (ResidualContext.source x).val).length+6)) (by
    intro row hr
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr
    exact ResidualActionRow.output_length a z ⟨x,v⟩)
  rw [value_length] at hb
  have hc := (ResidualContext.source x).val.counts_le_encoded_length
  exact le_trans hb (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionTable
