import Holant.Complexity.UniversalPairReduction.Reduction
import Holant.Proofs.Algorithms.TraceQueryControl

/-! A literal original-family programme for at most one directed paired pin.
The smoothing query removes the pin and reconnects its two incident native-X
edges, with the circle scalar retained. The two other queries replace the pin
by an actual fixed original-labelled binary graph and its reversed boundary.
In the symmetric case all three calls are the same smoothing query. Keeping
these repeated calls explicit gives one exact three-call transcript in all
cases, including empty inputs, zero answers, and a pin on a self-loop. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinProgramme
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open UniversalPairReduction SmoothingCompiler
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {d s : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
abbrev G := ValueJoins.signatures F T
abbrev inputEncoding := UniversalPairReduction.inputEncoding s a
abbrev queryEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev value := BinaryFamily.value (G F T) BinaryTable.delta

/-- The branch stores only an actual labelled graph or a statement about all
realizable binary graphs. No evaluation algorithm is supplied. -/
inductive Mode where
  | symmetric
      (h : ∀f : Signature K 2, Gadget.Realizes (BinaryFamily.family (G F T))
        .disequality f → f ![false,true]=f ![true,false])
  | asymmetric {S : NetworkShape 2} (L : Labelling S s 1 a)
      (h : QueryFamily.binary (G F T) L (Equiv.refl _) false true ≠
        QueryFamily.binary (G F T) L (Equiv.refl _) true false)

/-- The fixed programme is selected internally from the finite original
dictionary. Asymmetric free-wire factors are excluded by the existing actual
binary normalization theorem before an ordinary labelled graph is selected. -/
def mode : Mode F T := Classical.choice (by
  rcases actual_binary_dichotomy (BinaryFamily.family (G F T)) with hs|⟨W,hW,hE,ha⟩
  · exact ⟨Mode.symmetric hs⟩
  · let L := FiniteFamily.labelling (G F T) W hW
    have hL : L.sourceNetwork (G F T) (fun _ : Fin 1 => Signature.disequality)=W :=
      FiniteFamily.labelled_network (G F T) W hW hE
    apply Nonempty.intro
    apply Mode.asymmetric L
    simpa only [QueryFamily.binary_plus,hL] using ha)

variable (M : Mode F T)

def query (i : Fin 3) (r : UniversalPairReduction.Input s a) :
    ExactSignatureTables.Input s 1 a :=
  match M with
  | .symmetric _ => Surgery.query r
  | .asymmetric L _ =>
    if i=0 then Surgery.query r
    else if i=1 then OrderedQueries.plus L (forget s a r)
    else OrderedQueries.minus L (forget s a r)

def queryComputes (i : Fin 3) : Computes (inputEncoding (s:=s) (a:=a))
    (queryEncoding (s:=s) (a:=a)) (query F T M i) := by
  cases M with
  | symmetric hs => exact SmoothingCompiler.queryComputes s a
  | asymmetric L ha =>
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_
      (fun i => Fin.elim0 i) i) i) i
    · exact SmoothingCompiler.queryComputes s a
    · exact (forgetComputes s a).andThen (OrderedQueries.computes L (Equiv.refl _))
    · exact (forgetComputes s a).andThen (OrderedQueries.computes L (Equiv.swap 0 1))

def pre (r : UniversalPairReduction.Input s a) :=
  ([query F T M 0 r,query F T M 1 r,query F T M 2 r],flags r)

def preComputes : Computes (inputEncoding (s:=s) (a:=a))
    (OracleBatch.contextEncoding (queryEncoding (s:=s) (a:=a)) flagsEncoding)
    (pre F T M) :=
  pairComputes (Compiler.fixedListComputes (inputEncoding (s:=s) (a:=a))
    (queryEncoding (s:=s) (a:=a)) (fun r i => query F T M i r)
    (queryComputes F T M) [0,1,2]) flagsComputes

def collected (p : List K × Flags) : Collected (K:=K) :=
  (p.1.getD 0 0,(p.1.getD 1 0,(p.1.getD 2 0,p.2)))

def collectedComputes : Computes (OracleBatch.contextEncoding F.encoding flagsEncoding)
    (collectedEncoding F) (collected (K:=K)) := by
  let answers := Wiring.firstComputes (framedListEncoding F.encoding) flagsEncoding
  let entry := fun i => answers.andThen (Compiler.getDComputes F.encoding i 0)
  exact pairComputes (entry 0) (pairComputes (entry 1) (pairComputes (entry 2)
    (Wiring.secondComputes (framedListEncoding F.encoding) flagsEncoding)))

def post (p : List K × Flags) : K :=
  match M with
  | .symmetric _ => symmetricPost (p.1.getD 0 0,p.2)
  | .asymmetric L _ => asymmetricPost
      (QueryFamily.binary (G F T) L (Equiv.refl _) false true)
      (QueryFamily.binary (G F T) L (Equiv.refl _) true false) (collected p)

def postComputes : Computes (OracleBatch.contextEncoding F.encoding flagsEncoding)
    F.encoding (post F T M) := by
  cases M with
  | symmetric hs =>
    exact (pairComputes
      ((Wiring.firstComputes (framedListEncoding F.encoding) flagsEncoding).andThen
        (Compiler.getDComputes F.encoding 0 0))
      (Wiring.secondComputes (framedListEncoding F.encoding) flagsEncoding)).andThen
        (symmetricPostComputes F)
  | asymmetric L ha =>
    exact (collectedComputes F).andThen (asymmetricPostComputes F _ _)

variable (hn : ∀i b c,F.decode (T.edge i b c)=Signature.disequality b c)

include hn in
theorem recovery (r : UniversalPairReduction.Input s a) :
    value F T r=post F T M (OracleBatch.answers (T.evaluate F) (pre F T M r)) := by
  cases M with
  | symmetric hs =>
    simpa only [post,pre,query,OracleBatch.answers,List.map_cons,List.map_nil,
      List.getD_cons_zero,symmetricReducedValue] using ValueJoins.symmetric_exact F T hn hs r
  | asymmetric L ha =>
    simpa [post,pre,query,collected,OracleBatch.answers] using
      ValueJoins.asymmetric_exact F T hn L ha r

def reduction : PolyTimeOracleReduction (inputEncoding (s:=s) (a:=a)) F.encoding
    (queryEncoding (s:=s) (a:=a)) F.encoding (value F T) (T.evaluate F) :=
  OracleBatch.of_eq (preComputes F T M) (postComputes F T M) (T.outputBound F)
    (value F T) (recovery F T M hn)

theorem run_trace (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (a:=a)) F.encoding (T.evaluate F) oracle)
    (r : UniversalPairReduction.Input s a) :
    ∃n≤(reduction F T M hn).time.eval ((inputEncoding (s:=s) (a:=a)).encode r).length,
      OracleBatch.RunsTrace (reduction F T M hn).machine oracle
        ((reduction F T M hn).machine.init ((inputEncoding (s:=s) (a:=a)).encode r))
        ((reduction F T M hn).machine.output (F.encoding.encode (value F T r))) n
        ((pre F T M r).1.map (queryEncoding (s:=s) (a:=a)).encode) :=
  OracleBatch.of_eq_run_trace (preComputes F T M) (postComputes F T M)
    (T.outputBound F) (value F T) (recovery F T M hn) oracle ho r

def controlled : LengthControlledOracleReduction (inputEncoding (s:=s) (a:=a)) F.encoding
    (queryEncoding (s:=s) (a:=a)) F.encoding (value F T) (T.evaluate F) where
  reduction := reduction F T M hn
  targetOutput := T.outputBound F
  queryBound := (preComputes F T M).outputBound.bound
  safeQuery oracle ho r t c hr hq := by
    obtain ⟨n,_,htrace⟩ := run_trace F T M hn oracle ho r
    have hm := TraceQueryControl.transcript_member htrace t c hr hq
    obtain ⟨q,_,he⟩ := List.mem_map.mp hm
    refine ⟨q,he.symm,?_⟩
    exact (OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le (preComputes F T M) r).1

/-- Every successful run really makes three calls; zero and symmetric cases
keep their repeated calls, so the bound does not hide a primitive operation. -/
theorem exact_calls (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (a:=a)) F.encoding (T.evaluate F) oracle)
    (r : UniversalPairReduction.Input s a) :
    ∃n≤(reduction F T M hn).time.eval ((inputEncoding (s:=s) (a:=a)).encode r).length,
      ThreeQuery.queryCount (reduction F T M hn).machine oracle
        ((reduction F T M hn).machine.init ((inputEncoding (s:=s) (a:=a)).encode r)) n=3 := by
  obtain ⟨n,hn,htrace⟩ := run_trace F T M hn oracle ho r
  exact ⟨n,hn,by simpa only [pre,List.length_map,List.length_cons,List.length_nil] using htrace.count⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinProgramme
