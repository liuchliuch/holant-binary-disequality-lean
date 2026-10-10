import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationAccess
import Holant.Proofs.Hardness.GeneralEOSinglePinProgramme

/-! Same-field generic MWX Lemma 37. The exact target tables and their fixed
presentation are retained, so an original-field macro-elimination programme
can be composed without identifying generated-field presentations. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationProgramme
open Computability Holant Holant.Complexity Holant.Algebraic
open BinaryCompose UniversalPairReduction
namespace P
export GeneralEOSinglePinProgramme (G mode pre preComputes post postComputes recovery)
end P
namespace C
export GeneralEOSinglePinAmplificationCompiler (Input inputEncoding query queryComputes)
end C
namespace S
export GeneralEOSinglePinAmplificationSemantics (value query_value)
end S
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {d s : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
variable (hn : ∀i b c,F.decode (T.edge i b c)=Signature.disequality b c)
variable (j : Fin s)
variable (hE : (⟨a j.val,P.G F T j⟩ : AnySignature K)=⟨4,ExactTwoSignatures.E⟩)

abbrev Input := C.Input (s:=s) (a:=a)
abbrev inputEncoding := C.inputEncoding (s:=s) (a:=a)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev sourceValue := S.value (P.G F T)
abbrev amplified := C.query j.isLt (congrArg Sigma.fst hE)
abbrev selected := P.mode F T

def pre (r : Input (s:=s) (a:=a)) := P.pre F T (selected F T) (amplified F T j hE r)

def preComputes : Computes (inputEncoding (s:=s) (a:=a))
    (OracleBatch.contextEncoding (targetEncoding (s:=s) (a:=a)) SmoothingCompiler.flagsEncoding)
    (pre F T j hE) :=
  (C.queryComputes j.isLt (congrArg Sigma.fst hE)).andThen (P.preComputes F T (selected F T))

include hn hE in
theorem recovery (r : Input (s:=s) (a:=a)) :
    sourceValue F T r=P.post F T (selected F T)
      (OracleBatch.answers (T.evaluate F) (pre F T j hE r)) := by
  change S.value (P.G F T) r=_
  rw [←S.query_value (P.G F T) j hE r]
  exact P.recovery F T (selected F T) hn (amplified F T j hE r)

def reduction : PolyTimeOracleReduction (inputEncoding (s:=s) (a:=a)) F.encoding
    (targetEncoding (s:=s) (a:=a)) F.encoding (sourceValue F T) (T.evaluate F) :=
  OracleBatch.of_eq (preComputes F T j hE) (P.postComputes F T (selected F T))
    (T.outputBound F) (sourceValue F T) (recovery F T hn j hE)

theorem run_trace (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (a:=a)) F.encoding (T.evaluate F) oracle)
    (r : Input (s:=s) (a:=a)) :
    ∃n≤(reduction F T hn j hE).time.eval ((inputEncoding (s:=s) (a:=a)).encode r).length,
      OracleBatch.RunsTrace (reduction F T hn j hE).machine oracle
        ((reduction F T hn j hE).machine.init ((inputEncoding (s:=s) (a:=a)).encode r))
        ((reduction F T hn j hE).machine.output (F.encoding.encode (sourceValue F T r))) n
        ((pre F T j hE r).1.map (targetEncoding (s:=s) (a:=a)).encode) :=
  OracleBatch.of_eq_run_trace (preComputes F T j hE) (P.postComputes F T (selected F T))
    (T.outputBound F) (sourceValue F T) (recovery F T hn j hE) oracle ho r

/-- No generated-field equality or supplied counting evaluator is a premise.
Every target query denotes the unchanged literal table family T. -/
def source : LengthControlledOracleReduction (inputEncoding (s:=s) (a:=a)) F.encoding
    (targetEncoding (s:=s) (a:=a)) F.encoding (sourceValue F T) (T.evaluate F) where
  reduction := reduction F T hn j hE
  targetOutput := T.outputBound F
  queryBound := (preComputes F T j hE).outputBound.bound
  safeQuery oracle ho r t c hr hq := by
    obtain ⟨n,_,ht⟩ := run_trace F T hn j hE oracle ho r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t c hr hq
    obtain ⟨q,_,he⟩ := List.mem_map.mp hm
    refine ⟨q,he.symm,?_⟩
    exact (OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le (preComputes F T j hE) r).1

theorem exact_three_calls (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (a:=a)) F.encoding (T.evaluate F) oracle)
    (r : Input (s:=s) (a:=a)) :
    ∃n≤(source F T hn j hE).reduction.time.eval ((inputEncoding (s:=s) (a:=a)).encode r).length,
      ThreeQuery.queryCount (source F T hn j hE).reduction.machine oracle
        ((source F T hn j hE).reduction.machine.init ((inputEncoding (s:=s) (a:=a)).encode r)) n=3 := by
  obtain ⟨n,hbound,ht⟩ := run_trace F T hn j hE oracle ho r
  refine ⟨n,hbound,?_⟩
  change ThreeQuery.queryCount (reduction F T hn j hE).machine oracle
    ((reduction F T hn j hE).machine.init ((inputEncoding (s:=s) (a:=a)).encode r)) n=3
  simpa only [pre,GeneralEOSinglePinProgramme.pre,List.length_map,List.length_cons,List.length_nil] using ht.count

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationProgramme
