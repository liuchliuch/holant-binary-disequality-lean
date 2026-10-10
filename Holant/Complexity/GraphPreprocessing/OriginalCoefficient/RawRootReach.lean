import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootReachWiring
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawEdgeTable

/-! Raw closed-network bytes and a unary original vertex index to actual
reachability. The endpoint table and vertex count are physically derived once,
then fixed wire machines assemble the genuine root-initializer/BFS entry. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawRootReach
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) :=
  Σ r : {r : RawClosedNetwork // r.WellFormed s b arity}, Fin r.val.vertices.length
def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool :=
  sigmaEncoding (RawClosedNetwork.validatedEncoding s b arity)
    (fun r => OccurrenceLabel.unaryPortEncoding r.val.vertices.length)

variable {s b : ℕ} {arity : ℕ → ℕ}
def tableData (r : {r : RawClosedNetwork // r.WellFormed s b arity}) : List Bool × List Bool :=
  (List.replicate r.val.vertices.length true,BitmapIterate.edgeWord (r.val.graph r.property))
def prepared (x : Input s b arity) : RootReach.Input := ⟨⟨x.1.val.vertices.length,x.2⟩,(x.1.val.graph x.1.property).edges⟩
def value (x : Input s b arity) : List Bool :=
  NeighborPredicate.bitmap (x.1.val.graph x.1.property)
    ((x.1.val.graph x.1.property).reach x.2 x.1.val.vertices.length)

noncomputable def tableComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) RootReachWiring.pairWords tableData :=
  recode (RawEdgeTable.computes s b arity) id (fun _ => rfl) (fun _ => rfl)

noncomputable def prepareComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) RootReach.inputEncoding prepared :=
  recode ((leftMapComputes Frame.wordEncoding (tableComputes s b arity)).andThen RootReachWiring.computes)
    (fun x => (x.1,List.replicate x.2.val true)) (fun _ => rfl) (fun _ => rfl)

abbrev prepareMachine : Machine := (LeftMap.machine RawEdgeTable.machine).compose RootReachWiring.machine
abbrev machine : Machine := prepareMachine.compose RootReach.machine

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding value :=
  congrComputes ((prepareComputes s b arity).andThen RootReach.computes) (fun _ => rfl)

@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine := rfl
noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time

noncomputable def timed (x : Input s b arity) :
    TM2OutputsInTime machine.computer ((inputEncoding s b arity).encode x) (some (value x))
      ((timePolynomial s b arity).eval ((inputEncoding s b arity).encode x).length) := (computes s b arity).outputs x

theorem inFP : InFP (inputEncoding s b arity) Frame.wordEncoding value := (computes s b arity).inFP

theorem input_length_le_original (x : Input s b arity) :
    ((inputEncoding s b arity).encode x).length≤3*((RawClosedNetwork.encoding.encode x.1.val).length+1) := by
  have hc := x.1.val.counts_le_encoded_length
  have hi := x.2.isLt
  change (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode x.1.val)++List.replicate x.2.val true).length≤_
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

noncomputable def originalTimePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (timePolynomial s b arity).comp (3*(Polynomial.X+1))
noncomputable def timed_original (x : Input s b arity) :
    TM2OutputsInTime machine.computer ((inputEncoding s b arity).encode x) (some (value x))
      ((originalTimePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := (timed x).steps
  evals_in_steps := (timed x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (timePolynomial s b arity) (input_length_le_original x)
    exact le_trans (timed x).steps_le_m (by simpa [originalTimePolynomial] using h)

noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  originalTimePolynomial s b arity*Polynomial.C machine.primitiveBudget
theorem primitive_bound (x : Input s b arity) :
    primitiveCost machine (timed_original x).steps (some (initList machine.computer ((inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed_original x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

@[simp] theorem value_length (x : Input s b arity) : (value x).length=x.1.val.vertices.length := by simp [value,RawClosedNetwork.graph]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawRootReach
