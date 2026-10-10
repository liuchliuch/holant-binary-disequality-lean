import Holant.Proofs.Recognition.RuntimeTensorRequestSource

/-! A single original-root search programme for an addressed transformed entry.
The entire layout, selected label, output word and identity/K/KX mode are tape
data. Matrix pins and original bindings are generated internally. The retained
packet is present exactly when the prescribed transformed entry is zero. This
is the runtime support-test primitive; no full EO criterion is asserted here. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEntryProbe
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev Input := RuntimeTensorRequest.Input × RuntimeTensorRows.Word
abbrev encoding := pairEncoding RuntimeTensorRequest.encoding RuntimeTensorRows.wordEncoding

def body (r : Input) : RationalInputMachine.Body :=
  RuntimeTensorBasis.rows (RuntimeTensorRequest.basisInput r.1) ++
    [RuntimeTensorRows.value (RuntimeTensorRequest.rowInput r.1) r.2]
def request (r : Input) : RationalInputMachine.Input where
  «variables» := RuntimeTensorRequest.width r.1
  original := OriginalFamilyPackingMachine.roots (RuntimeTensorRequest.source r.1)
  body := body r
  addresses := OriginalAllocatedPackingMachine.addresses (RuntimeTensorRequest.allocated r.1)

def context := RuntimeTensorRows.fst RuntimeTensorRequest.encoding RuntimeTensorRows.wordEncoding
def word := RuntimeTensorRows.snd RuntimeTensorRequest.encoding RuntimeTensorRows.wordEncoding

def bodyExecutes : Executes encoding RationalInputMachine.bodyEncoding body := by
  let basis := (context.comp (Executes.ofComputes RuntimeTensorRequest.basisComputes)).comp RuntimeTensorBasis.executes
  let entry := ((context.comp RuntimeTensorRequest.rowExecutes).pair word).comp RuntimeTensorRows.valueExecutes
  let row := entry.comp (Executes.ofComputes (NegativeCertificateMachine.Lists.singleton RationalSparseMachine.encoding))
  exact (basis.pair row).comp (Executes.ofComputes (WireLists.append RationalSparseMachine.encoding))

def executes : Executes encoding RationalInputMachine.encoding request := by
  let width := context.comp (Executes.ofComputes RuntimeTensorRequest.widthComputes)
  let roots := context.comp (Executes.ofComputes
    (RuntimeTensorRequest.sourceComputes.andThen OriginalFamilyPackingMachine.rootsComputes))
  let addresses := (context.comp (Executes.ofComputes RuntimeTensorRequest.allocatedComputes)).comp
    OriginalAllocatedPackingMachine.addressesExecutes
  exact Executes.recode (width.pair (roots.pair (bodyExecutes.pair addresses))) id (fun _ => rfl) (fun _ => rfl)

def machine : BinaryCompose.Machine := executes.machine.compose WitnessOutput.originalMachine

open RuntimeTensorRequestSource (Width Extra address bindings typedBasis Bound transformed)
variable {s : ℕ} (arity : Fin s → ℕ) (input : OriginalFamilyInput.Input arity)
variable (native opposite : Bool) (i : Fin s) (x : Fin (arity i) → Bool)

def dummy : RuntimeTensorRequest.Candidate := (true,[],[],[])
def encode : Input := (RuntimeTensorRequestSource.encode arity input native opposite i dummy,List.ofFn x)
def typedBody : List (Sparse.Poly (Width arity) 1) :=
  typedBasis arity native opposite ++ [RuntimeTensorRowsSoundness.entries (address arity i) x]

theorem body_wire : body (encode arity input native opposite i x)=
    RationalInputMachine.bodyWire (typedBody arity native opposite i x) := by
  unfold body encode
  rw [RuntimeTensorRequestSource.basisInput_exact,RuntimeTensorBasis.rows_wire,
    RuntimeTensorRequestSource.rowInput_exact,RuntimeTensorRowsSoundness.value_wire]
  rfl

theorem request_exact : request (encode arity input native opposite i x)=
    RationalInputMachine.fromSource (UniformKPolynomial.descriptors arity input)
      (typedBody arity native opposite i x) (bindings arity) := by
  unfold request RationalInputMachine.fromSource
  congr 1
  · exact RuntimeTensorRequestSource.width_exact arity input native opposite i dummy
  · exact OriginalFamilyPackingSource.roots_exact arity input false
  · exact body_wire arity input native opposite i x
  · exact OriginalAllocatedPackingMachine.addresses_source arity input false 1

theorem guard_mem : SparseTransform.guard RationalCompiler.data (Extra arity) ∈
    typedBody arity native opposite i x := by
  simp [typedBody,typedBasis,RuntimeTensorBasis.typedRows]

variable (G : (j : Fin s) → Signature AlgebraicComplex (arity j))
  (represented : ∀j y,(input j y).Represents (G j y : ℂ))

def output : Option WitnessOutput.Output :=
  WitnessOutput.originalOutput (UniformKPolynomial.descriptors arity input)
    (UniformKPolynomial.valid arity G input represented)
    (typedBody arity native opposite i x) (bindings arity)

theorem source_outputs : ∃ticks,Nonempty (TM2OutputsInTime machine.computer
    (encoding.encode (encode arity input native opposite i x))
    (some (WitnessOutput.resultEncoding.encode (output arity input native opposite i x G represented))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := WitnessOutput.original_outputs
    (UniformKPolynomial.descriptors arity input) (UniformKPolynomial.valid arity G input represented)
    (typedBody arity native opposite i x) (bindings arity)
  have left := executes.outputs (encode arity input native opposite i x)
  rw [request_exact arity input native opposite i x] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩

theorem output_isSome_iff :
    (output arity input native opposite i x G represented).isSome=true ↔
      ∃z : Fin (Width arity) → ℂ, Bound arity G z ∧
        ∀p∈typedBody arity native opposite i x,
          SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 := by
  rw [output,WitnessOutput.originalOutput_correct _ _ (UniformKPolynomial.values arity G)
    (UniformKPolynomial.descriptors_represents arity G input represented) _ _
      (guard_mem arity native opposite i x)]
  apply exists_congr
  intro z
  exact RationalInputSystem.system_zero_iff (fun j => (UniformKPolynomial.values arity G j : ℂ))
    (typedBody arity native opposite i x) (bindings arity) z

theorem output_correct :
    (output arity input native opposite i x G represented).isSome=true ↔
      transformed arity native opposite i G x=0 := by
  rw [output_isSome_iff]
  constructor
  · rintro ⟨z,hb,hr⟩
    obtain ⟨hB,hx⟩ := List.forall_mem_append.mp hr
    have he := hx (RuntimeTensorRowsSoundness.entries (address arity i) x) (by simp)
    rw [RuntimeTensorRequestSource.entries_exact arity native opposite i G z hb hB x] at he
    exact Subtype.ext he
  · intro hx
    let z := RuntimeTensorRequestSource.fill arity native opposite G 0
    have hb : Bound arity G z := RuntimeTensorRequestSource.fill_bound arity native opposite G 0
    have hB : ∀p∈typedBasis arity native opposite,
        SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 :=
      RuntimeTensorRequestSource.fill_basis arity native opposite G 0
    refine ⟨z,hb,List.forall_mem_append.mpr ⟨hB,?_⟩⟩
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    rw [RuntimeTensorRequestSource.entries_exact arity native opposite i G z hb hB x,hx]
    rfl

def cost : ℕ := Classical.choose (source_outputs arity input native opposite i x G represented)
def execution : TM2OutputsInTime machine.computer (encoding.encode (encode arity input native opposite i x))
    (some (WitnessOutput.resultEncoding.encode (output arity input native opposite i x G represented)))
    (cost arity input native opposite i x G represented) :=
  Classical.choice (Classical.choose_spec (source_outputs arity input native opposite i x G represented))

/-- Positive bytes are the actual original-root search candidate serialization. -/
theorem returned_packet (o : WitnessOutput.Output)
    (ho : output arity input native opposite i x G represented=some o) :
    ∃a : OriginalSystemWitness.Candidate (m:=RuntimeTensorRequestSource.Entries arity+2)
        (typedBody arity native opposite i x),
      OriginalSystemWitness.candidate (UniformKPolynomial.descriptors arity input)
        (UniformKPolynomial.valid arity G input represented) (typedBody arity native opposite i x)
        (bindings arity)=some a ∧ o=WitnessOutput.ofCandidate a := by
  obtain ⟨a,ha,ho⟩ := Option.map_eq_some_iff.mp ho
  exact ⟨a,ha,ho.symm⟩

/-- Primitive operations and every stack prefix of the same complete
request-compilation plus RootCode-search programme. -/
theorem resources :
    primitiveCost machine (execution arity input native opposite i x G represented).steps
      (some (initList machine.computer
        (encoding.encode (encode arity input native opposite i x)))) ≤
      cost arity input native opposite i x G represented*machine.primitiveBudget ∧
    ∀k,k≤(execution arity input native opposite i x G represented).steps →
      ∀cfg : machine.Config,
      (fun st => st.bind machine.computer.step)^[k]
        (some (initList machine.computer
          (encoding.encode (encode arity input native opposite i x))))=some cfg →
      stackSize cfg.stk ≤ (encoding.encode (encode arity input native opposite i x)).length +
        cost arity input native opposite i x G represented*machine.primitiveBudget := by
  constructor
  · exact (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _
      (execution arity input native opposite i x G represented).steps_le_m)
  · intro k hk cfg hc
    have h := machine.run_size_le
      (initList machine.computer
        (encoding.encode (encode arity input native opposite i x))) cfg k hc
    rw [Machine.size_init] at h
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _
      (hk.trans (execution arity input native opposite i x G represented).steps_le_m)) _)

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEntryProbe
