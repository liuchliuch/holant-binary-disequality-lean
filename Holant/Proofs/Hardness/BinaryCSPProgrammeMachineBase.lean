import Holant.Proofs.Hardness.BinaryCSPProgrammeValue
import Holant.Proofs.Hardness.ThreeModeFilterExecution
import Holant.Complexity.OracleBatch.ReductionTrace

/-! Literal query/root preprocessing for unsigned support counting. The
zeroth moment is computed as 2^variables in the original coefficient field.
Only positive-copy graphs are sent to the oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot BinaryCSPProgrammeCore
namespace Q
export BinaryCSPProgrammeRepeat (queries queriesComputes sampleCount expand)
end Q
namespace R
export BinaryCSPProgrammeRoots (roots rootsComputes roots_bound)
end R
namespace V
export BinaryCSPProgrammeValue (value base coordinates base_unit base_minus base_two decode_coordinates
  counts_le_bytes answer_bound targetOutput)
end V
namespace S
export ThreeModeFilter (State encoding Bounded)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b c : K) (f : Bool→Bool→K)

abbrev contextEncoding := pairEncoding (framedListEncoding F.encoding) F.encoding
abbrev answerEncoding := OracleBatch.contextEncoding F.encoding (contextEncoding F)
abbrev initializedEncoding := pairEncoding (S.encoding F) F.encoding

def total (r : Raw) : K := 2^r.variables
def context (r : Raw) : List K × K := (R.roots a b c r.edges.length,total r)

def totalComputes : Computes encoding F.encoding (total (K:=K)) :=
  variablesComputes.andThen (ThreeModeProgrammeRoots.powerComputes F 2)

def contextComputes : Computes encoding (contextEncoding F) (context a b c) :=
  pairComputes (edgeCountComputes.andThen (R.rootsComputes F a b c)) (totalComputes F)

def preprocessing (r : Raw) : List Raw × (List K × K) := (Q.queries r,context a b c r)
def pre : Computes encoding (OracleBatch.contextEncoding encoding (contextEncoding F))
    (preprocessing a b c) := pairComputes Q.queriesComputes (contextComputes F a b c)

def answers (r : Raw) : List K := (Q.queries r).map (V.value f)
def answered (r : Raw) : List K × (List K × K) := (answers f r,context a b c r)
def state (r : Raw) : S.State K :=
  ((R.roots a b c r.edges.length,total r::answers f r),(0,1))

def initializeComputes : Computes (answerEncoding F) (initializedEncoding F)
    (fun z : List K × (List K × K) => (((z.2.1,z.2.2::z.1),(0,1)),z.2.2)) := by
  let ys := Wiring.firstComputes (framedListEncoding F.encoding) (contextEncoding F)
  let ctx := Wiring.secondComputes (framedListEncoding F.encoding) (contextEncoding F)
  let roots := ctx.andThen (Wiring.firstComputes (framedListEncoding F.encoding) F.encoding)
  let card := ctx.andThen (Wiring.secondComputes (framedListEncoding F.encoding) F.encoding)
  let moments := (pairComputes card ys).andThen
    (Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.cons F.encoding)
  let scalars := pairComputes (constantComputes (answerEncoding F) F.encoding 0)
    (constantComputes (answerEncoding F) F.encoding 1)
  exact pairComputes (pairComputes (pairComputes roots moments) scalars) card

abbrev transcriptBound := OracleBatch.decoderBound (pre F a b c) (V.targetOutput F a b c f)
def stateBound : Polynomial ℕ := (initializeComputes F).outputBound.bound.comp (transcriptBound F a b c f)
def answerBudget : Polynomial ℕ := Q.queriesComputes.outputBound.bound
def rootBudget : Polynomial ℕ := 3*Polynomial.X
def initialBudget : Polynomial ℕ := answerBudget+Polynomial.X+1

theorem answered_length (r : Raw) :
    ((answerEncoding F).encode (answered a b c f r)).length≤
      (transcriptBound F a b c f).eval (encoding.encode r).length :=
  OracleBatch.decoder_length_le (pre F a b c) (V.targetOutput F a b c f) r

theorem initialized_length (r : Raw) :
    ((initializedEncoding F).encode (state a b c f r,total r)).length≤
      (stateBound F a b c f).eval (encoding.encode r).length := by
  have h := (initializeComputes F).outputBound.length_le (answered a b c f r)
  exact h.trans (by
    simpa only [stateBound,Polynomial.eval_comp] using natPolynomial_eval_mono
      (initializeComputes F).outputBound.bound (answered_length F a b c f r))

theorem state_length (r : Raw) :
    ((S.encoding F).encode (state a b c f r)).length≤
      (stateBound F a b c f).eval (encoding.encode r).length := by
  have h := initialized_length F a b c f r
  rw [pairEncoding_length] at h
  dsimp only [Prod.fst,Prod.snd] at h
  omega

theorem answer_bound (r : Raw) (y : K) (hy : y∈answers f r) :
    ArithmeticSize.Bound (V.base a b c f)
      (answerBudget.eval (encoding.encode r).length) y := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hy
  have hmem := OracleBatch.member_length_le ((Q.queries r).map encoding.encode)
    (encoding.encode q) (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hlist := Q.queriesComputes.outputBound.length_le r
  rw [OracleBatch.list_encode] at hlist
  exact (V.answer_bound a b c f q).mono (.inl 4) (V.base_unit a b c f)
    (by have h := V.counts_le_bytes q; dsimp only [answerBudget]; omega)

theorem total_bound (r : Raw) :
    ArithmeticSize.Bound (V.base a b c f) r.variables (total (K:=K) r) := by
  have h : ArithmeticSize.Bound (V.base a b c f) 1 (2 : K) := by
    simpa only [V.base_two] using
      (ArithmeticSize.Bound.coefficient (coeff:=V.base a b c f) (.inl 5))
  exact ThreeModeProgrammeRootBounds.power_bound _ h _

theorem initial_bounded (r : Raw) :
    S.Bounded (fun i => F.decode (V.coordinates F a b c f i))
      (rootBudget.eval (encoding.encode r).length)
      (initialBudget.eval (encoding.encode r).length) (state a b c f r) := by
  simp only [S.Bounded,V.decode_coordinates]
  have hsize := V.counts_le_bytes r
  have ha : ArithmeticSize.Bound (V.base a b c f) 1 a :=
    ArithmeticSize.Bound.coefficient (coeff:=V.base a b c f) (.inl 0)
  have hb : ArithmeticSize.Bound (V.base a b c f) 1 b :=
    ArithmeticSize.Bound.coefficient (coeff:=V.base a b c f) (.inl 1)
  have hc : ArithmeticSize.Bound (V.base a b c f) 1 c :=
    ArithmeticSize.Bound.coefficient (coeff:=V.base a b c f) (.inl 2)
  refine ⟨?_,?_,ArithmeticSize.Bound.zero (coeff:=V.base a b c f) (.inl 4) _,?_⟩
  · intro x hx
    exact (R.roots_bound a b c (V.base a b c f) (.inl 4) (V.base_unit a b c f)
      ha hb hc r.edges.length x hx).mono (.inl 4) (V.base_unit a b c f)
        (by simp only [rootBudget,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]; omega)
  · intro y hy
    obtain rfl | hy := List.mem_cons.mp hy
    · exact (total_bound a b c f r).mono (.inl 4) (V.base_unit a b c f)
        (by simp only [initialBudget,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]; omega)
    · exact (answer_bound a b c f r y hy).mono (.inl 4) (V.base_unit a b c f)
        (by simp only [initialBudget,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]; omega)
  · exact ArithmeticSize.Bound.one.mono (.inl 4) (V.base_unit a b c f) (Nat.zero_le _)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeMachine
