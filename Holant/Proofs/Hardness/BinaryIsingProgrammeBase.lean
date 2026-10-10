import Holant.Proofs.Hardness.BinaryIsingQuery
import Holant.Proofs.Hardness.BinaryIsingUnnormalized
import Holant.Proofs.Hardness.ThreeModeFilterExecution
import Holant.Complexity.OracleBatch.ReductionTrace

/-! Concrete Ising root and positive-query preprocessing. The input keeps its
literal graph codec; the query adds only a unary repetition counter. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingProgramme
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot BinaryCSPProgrammeCore
namespace Q
export BinaryIsingQuery (Query queryEncoding value base coordinates base_unit base_minus base_two
  base_scalar base_ratio decode_coordinates budget sizePolynomial budget_le answer_bound targetOutput)
end Q
namespace U
export BinaryIsingUnnormalized (roots)
end U
namespace S
export ThreeModeFilter (State encoding Bounded)
end S
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate succComputes)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (p q : K)

abbrev contextEncoding := pairEncoding (framedListEncoding F.encoding) (pairEncoding F.encoding F.encoding)
abbrev answerEncoding := OracleBatch.contextEncoding F.encoding (contextEncoding F)

def queries (r : Raw) : List Q.Query := (List.range r.edges.length).map (fun k=>(r,k))
def queriesComputes : Computes encoding (framedListEncoding Q.queryEncoding) queries :=
  W.tabulate encoding Q.queryEncoding (fun r=>r.edges.length) edgeCountComputes _
    (pairComputes (Wiring.firstComputes encoding unary) (Wiring.secondComputes encoding unary))

@[simp] theorem queries_length (r : Raw) : (queries r).length=r.edges.length := by simp [queries]

def desired (r : Raw) : K := BinaryIsingWeights.scalar p q r.edges.length
def total (r : Raw) : K := 2^(r.variables+1)
def roots (r : Raw) : List K := U.roots (desired p q r) (q/p) r.edges.length
def context (r : Raw) : List K×(K×K) := (roots p q r,(desired p q r,total r))

def rootComputes : Computes (pairEncoding unary unary) F.encoding
    (fun a : ℕ×ℕ=>(p^2*q)^a.1*(q/p)^(2*(a.2+1))) := by
  let m := Wiring.firstComputes unary unary
  let j := (Wiring.secondComputes unary unary).andThen W.succComputes
  let twice : Computes (pairEncoding unary unary) unary (fun a : ℕ×ℕ=>2*(a.2+1)) :=
    congrComputes ((pairComputes j j).andThen ThreeModeProgrammeRoots.U.addComputes)
      (fun a=>by change (a.2+1)+(a.2+1)=2*(a.2+1); omega)
  exact (pairComputes (m.andThen (ThreeModeProgrammeRoots.powerComputes F (p^2*q)))
    (twice.andThen (ThreeModeProgrammeRoots.powerComputes F (q/p)))).andThen
      (Concrete.fieldMultiplication F)

def rootsComputes : Computes encoding (framedListEncoding F.encoding) (roots p q) := by
  let rows := W.tabulate unary F.encoding id (identityComputes unary)
    (fun m j=>(p^2*q)^m*(q/p)^(2*(j+1))) (rootComputes F p q)
  exact congrComputes (edgeCountComputes.andThen rows) (fun r=>by
    simp [roots,desired,U.roots,BinaryIsingFilter.roots,BinaryIsingWeights.scalar,
      List.map_map,Function.comp_def])

def desiredComputes : Computes encoding F.encoding (desired p q) :=
  edgeCountComputes.andThen (ThreeModeProgrammeRoots.powerComputes F (p^2*q))
def totalComputes : Computes encoding F.encoding (total (K:=K)) :=
  (variablesComputes.andThen W.succComputes).andThen (ThreeModeProgrammeRoots.powerComputes F 2)
def contextComputes : Computes encoding (contextEncoding F) (context p q) :=
  pairComputes (rootsComputes F p q) (pairComputes (desiredComputes F p q) (totalComputes F))
def preprocessing (r : Raw) : List Q.Query×(List K×(K×K)) := (queries r,context p q r)
def pre : Computes encoding (OracleBatch.contextEncoding Q.queryEncoding (contextEncoding F))
    (preprocessing p q) := pairComputes queriesComputes (contextComputes F p q)

def answers (r : Raw) : List K := (queries r).map (Q.value p q)
def answered (r : Raw) : List K×(List K×(K×K)) := (answers p q r,context p q r)
def state (r : Raw) : S.State K := ((roots p q r,total r::answers p q r),(desired p q r,1))

def initializeComputes : Computes (answerEncoding F) (S.encoding F)
    (fun z : List K×(List K×(K×K))=>((z.2.1,z.2.2.2::z.1),(z.2.2.1,1))) := by
  let ys := Wiring.firstComputes (framedListEncoding F.encoding) (contextEncoding F)
  let ctx := Wiring.secondComputes (framedListEncoding F.encoding) (contextEncoding F)
  let rs := ctx.andThen (Wiring.firstComputes (framedListEncoding F.encoding) (pairEncoding F.encoding F.encoding))
  let numbers := ctx.andThen (Wiring.secondComputes (framedListEncoding F.encoding) (pairEncoding F.encoding F.encoding))
  let des := numbers.andThen (Wiring.firstComputes F.encoding F.encoding)
  let card := numbers.andThen (Wiring.secondComputes F.encoding F.encoding)
  let moments := (pairComputes card ys).andThen
    (Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.cons F.encoding)
  exact pairComputes (pairComputes rs moments)
    (pairComputes des (constantComputes (answerEncoding F) F.encoding 1))

abbrev transcriptBound := OracleBatch.decoderBound (pre F p q) (Q.targetOutput F p q)
def stateBound : Polynomial ℕ := (initializeComputes F).outputBound.bound.comp (transcriptBound F p q)
def answerBudget : Polynomial ℕ := Q.sizePolynomial.comp queriesComputes.outputBound.bound
def rootBudget : Polynomial ℕ := 3*Polynomial.X
def initialBudget : Polynomial ℕ := answerBudget+Polynomial.X+1

theorem answered_length (r : Raw) :
    ((answerEncoding F).encode (answered p q r)).length≤
      (transcriptBound F p q).eval (encoding.encode r).length :=
  OracleBatch.decoder_length_le (pre F p q) (Q.targetOutput F p q) r

theorem state_length (r : Raw) : ((S.encoding F).encode (state p q r)).length≤
    (stateBound F p q).eval (encoding.encode r).length := by
  have h := (initializeComputes F).outputBound.length_le (answered p q r)
  exact h.trans (by simpa only [stateBound,Polynomial.eval_comp] using
    natPolynomial_eval_mono (initializeComputes F).outputBound.bound (answered_length F p q r))

omit [Algebra ℚ K] in
theorem roots_bound (r : Raw) (x : K) (hx : x∈roots p q r) :
    ArithmeticSize.Bound (Q.base p q) (3*r.edges.length) x := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
  have hj' := List.mem_range.mp hj
  have hc : ArithmeticSize.Bound (Q.base p q) 1 (p^2*q) :=
    ArithmeticSize.Bound.coefficient (coeff:=Q.base p q) (.inl 2)
  have hr : ArithmeticSize.Bound (Q.base p q) 1 (q/p) :=
    ArithmeticSize.Bound.coefficient (coeff:=Q.base p q) (.inl 3)
  exact ((ThreeModeProgrammeRootBounds.power_bound _ hc r.edges.length).mul
    (ThreeModeProgrammeRootBounds.power_bound _ hr (2*(j+1)))).mono (.inl 4) (Q.base_unit p q) (by omega)

omit [Algebra ℚ K] in
theorem answer_bound (r : Raw) (y : K) (hy : y∈answers p q r) :
    ArithmeticSize.Bound (Q.base p q) (answerBudget.eval (encoding.encode r).length) y := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
  have hm := OracleBatch.member_length_le ((queries r).map Q.queryEncoding.encode)
    (Q.queryEncoding.encode a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hl := queriesComputes.outputBound.length_le r
  rw [OracleBatch.list_encode] at hl
  have hb := natPolynomial_eval_mono Q.sizePolynomial (hm.trans hl)
  exact (Q.answer_bound p q a).mono (.inl 4) (Q.base_unit p q) ((Q.budget_le a).trans (by
    simpa only [answerBudget,Polynomial.eval_comp] using hb))

omit [Algebra ℚ K] in
theorem total_bound (r : Raw) : ArithmeticSize.Bound (Q.base p q) (r.variables+1) (total (K:=K) r) :=
  ThreeModeProgrammeRootBounds.power_bound _
    (ArithmeticSize.Bound.coefficient (coeff:=Q.base p q) (.inl 6)) _

omit [Algebra ℚ K] in
theorem desired_bound (r : Raw) : ArithmeticSize.Bound (Q.base p q) r.edges.length (desired p q r) :=
  ThreeModeProgrammeRootBounds.power_bound _
    (ArithmeticSize.Bound.coefficient (coeff:=Q.base p q) (.inl 2)) _

theorem initial_bounded (r : Raw) :
    S.Bounded (fun i=>F.decode (Q.coordinates F p q i))
      (rootBudget.eval (encoding.encode r).length)
      (initialBudget.eval (encoding.encode r).length) (state p q r) := by
  simp only [S.Bounded,Q.decode_coordinates]
  have hsize := BinaryCSPProgrammeValue.counts_le_bytes r
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    exact (roots_bound p q r x hx).mono (.inl 4) (Q.base_unit p q)
      (by simp only [rootBudget,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]; omega)
  · intro y hy
    obtain rfl|hy := List.mem_cons.mp hy
    · exact (total_bound p q r).mono (.inl 4) (Q.base_unit p q)
        (by simp only [initialBudget,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]; omega)
    · exact (answer_bound p q r y hy).mono (.inl 4) (Q.base_unit p q)
        (by simp only [initialBudget,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]; omega)
  · exact (desired_bound p q r).mono (.inl 4) (Q.base_unit p q)
      (by simp only [rootBudget,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]; omega)
  · exact ArithmeticSize.Bound.one.mono (.inl 4) (Q.base_unit p q) (Nat.zero_le _)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingProgramme
