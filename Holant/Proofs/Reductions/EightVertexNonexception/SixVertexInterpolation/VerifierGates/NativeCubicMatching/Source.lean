import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Renderer
import Holant.Proofs.Algorithms.TraceQueryControl


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Source
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryInterpolation Holant.Complexity.OracleBatch
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open UniversalPairReduction.ThreeQuery
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.CountingHardness.VerifierCompiler.Stateful.CapacityFrontend
open WeightedMatchingInterpolation
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev F := Programs.F
abbrev TargetInput := Semantics.TargetInput
abbrev targetEncoding := Semantics.targetEncoding
abbrev targetValue := Semantics.targetValue
namespace Old
export Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Source (zero_value one_value)
export Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Programs (vertices zero)
end Old

theorem palette_zero_one (i : Fin 2) (x : Fin (arity i.val) → Bool) :
    palette i x=0 ∨ palette i x=1 := by
  have ho (y : Fin 3 → Bool) : ONE y=0 ∨ ONE y=1 := by
    rw [one_ternary]
    unfold OldTree.ternary
    split_ifs <;> simp
  fin_cases i
  · simpa [palette] using ho x
  · simpa [palette,TWO] using ho (fun i => !x i)
theorem palette_indicator (i : Fin 2) (x : Fin (arity i.val) → Bool) :
    palette i x=if palette i x=1 then 1 else 0 := by
  rcases palette_zero_one i x with h | h <;> simp [h]
def Supported (r : TargetInput) (z : (Fin r.val.edges.length × Bool) → Bool) : Prop :=
  (∀ v : Fin r.val.vertices.length,palette (r.val.signatureLabel r.property v)
    ((r.val.shape r.property).assignment Fin.elim0 z v)=1) ∧
  (∀ e : Fin r.val.edges.length,z (e,false)≠z (e,true))

/-- Every legal target graph, including actual self-loops and parallel edges,
is a count of supported HALF-END assignments. Thus answer size is produced
from the target language itself, not from expected oracle answers. -/
theorem target_count (r : TargetInput) :
    ∃ n : ℕ,n≤2^(2*r.val.edges.length) ∧ targetValue r=(n : ℚ) := by
  let n := Fintype.card {z : (Fin r.val.edges.length × Bool) → Bool // Supported r z}
  refine ⟨n,?_,?_⟩
  · have h := Fintype.card_subtype_le (Supported r)
    simpa only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,mul_comm] using h
  · change (∑ z : (Fin r.val.edges.length × Bool) → Bool,
      (∏ v : Fin r.val.vertices.length,palette (r.val.signatureLabel r.property v)
        ((r.val.shape r.property).assignment Fin.elim0 z v)) *
        (∏ e : Fin r.val.edges.length,Signature.disequality (z (e,false)) (z (e,true))))=(n : ℚ)
    have hterm (z : (Fin r.val.edges.length × Bool) → Bool) :
        (∏ v : Fin r.val.vertices.length,palette (r.val.signatureLabel r.property v)
          ((r.val.shape r.property).assignment Fin.elim0 z v)) *
          (∏ e : Fin r.val.edges.length,Signature.disequality (z (e,false)) (z (e,true)))=
            if Supported r z then (1 : ℚ) else 0 := by
      have hvprod : (∏ v : Fin r.val.vertices.length,palette (r.val.signatureLabel r.property v)
          ((r.val.shape r.property).assignment Fin.elim0 z v))=
            if ∀ v : Fin r.val.vertices.length,palette (r.val.signatureLabel r.property v)
              ((r.val.shape r.property).assignment Fin.elim0 z v)=1 then (1 : ℚ) else 0 := by
        calc
          _ = ∏ v : Fin r.val.vertices.length,
              if palette (r.val.signatureLabel r.property v)
                ((r.val.shape r.property).assignment Fin.elim0 z v)=1 then (1 : ℚ) else 0 := by
            apply Finset.prod_congr rfl
            intro v _
            exact palette_indicator _ _
          _ = _ := by
            rw [Fintype.prod_boole]
            split_ifs <;> rfl
      rw [hvprod]
      simp only [Signature.disequality,Fintype.prod_boole]
      by_cases hv : ∀ v : Fin r.val.vertices.length,palette (r.val.signatureLabel r.property v)
        ((r.val.shape r.property).assignment Fin.elim0 z v)=1
      all_goals by_cases he : ∀ e : Fin r.val.edges.length,z (e,false)≠z (e,true)
      all_goals simp [Supported,hv,he]
    simp_rw [hterm]
    dsimp only [n]
    rw [Fintype.card_subtype]
    exact Finset.sum_boole _ _

def targetOutput : PolynomialOutputBound targetEncoding F.encoding targetValue where
  bound := (RingFormulaMachine.widthPolynomial F (Postprocess.coordinates F)).comp (2*Polynomial.X)
  length_le r := by
    obtain ⟨n,hn,hv⟩ := target_count r
    rw [hv]
    have he : r.val.edges.length≤(targetEncoding.encode r).length := by
      have h := r.val.counts_le_encoded_length
      change r.val.edges.length≤(RawClosedNetwork.encoding.encode r.val).length
      omega
    have hpow : n≤2^(2*(targetEncoding.encode r).length) :=
      hn.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 he))
    have h := (Postprocess.count_bound F n (2*(targetEncoding.encode r).length) hpow).encoded_length_le F
      (Postprocess.coordinates F)
    simpa only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,RingFormulaMachine.width_eval] using h

def emptyTest : Computes unitEncoding encodingBoolBool (fun g : UnitInput => decide (g.val.1=0)) :=
  (pairComputes Old.vertices (constantComputes unitEncoding UnaryBinary.unaryEncoding 0)).andThen
    (equalComputes UnaryBinary.unaryEncoding)
def queries (g : UnitInput) : List TargetInput :=
  if g.val.1=0 then [] else if OldCompiler.zeroTest g then [] else [Layout.query g]
def known (g : UnitInput) : ℚ := if g.val.1=0 then 1 else 0
def metadataEncoding := pairEncoding F.encoding UnaryBinary.unaryEncoding
def metadata (g : UnitInput) : ℚ × ℕ := (known g,Incidence.paddingCount g)
def pre (g : UnitInput) : List TargetInput × (ℚ × ℕ) := (queries g,metadata g)
def queryList : Computes unitEncoding (framedListEncoding targetEncoding) queries := by
  let empty := constantComputes unitEncoding (framedListEncoding targetEncoding) []
  let singleton := fixedListComputes unitEncoding targetEncoding
    (fun g (_ : Fin 1) => Layout.query g) (fun _ => Renderer.Code.computes) [0]
  exact congrComputes (ifComputes emptyTest empty (ifComputes Old.zero empty singleton))
    (fun _ => by simp [queries])
def knownComputes : Computes unitEncoding F.encoding known :=
  congrComputes (ifComputes emptyTest (constantComputes unitEncoding F.encoding 1)
    (constantComputes unitEncoding F.encoding 0)) (fun _ => by simp [known])
def preprocess : Computes unitEncoding (OracleBatch.contextEncoding targetEncoding metadataEncoding) pre :=
  pairComputes queryList (pairComputes knownComputes Programs.paddingCount)

def answerEncoding := OracleBatch.contextEncoding F.encoding metadataEncoding
def post (x : List ℚ × (ℚ × ℕ)) : ℚ :=
  if x.1=[] then x.2.1 else x.1.getD 0 0*((2 : ℚ)⁻¹)^x.2.2
def postprocess : Computes answerEncoding F.encoding post := by
  let ys := Wiring.firstComputes (framedListEncoding F.encoding) metadataEncoding
  let «meta» := Wiring.secondComputes (framedListEncoding F.encoding) metadataEncoding
  let len := ys.andThen (WireLists.lengthComputes F.encoding)
  let empty := (pairComputes len (constantComputes answerEncoding UnaryBinary.unaryEncoding 0)).andThen
    (equalComputes UnaryBinary.unaryEncoding)
  let known := «meta».andThen (Wiring.firstComputes F.encoding UnaryBinary.unaryEncoding)
  let power := «meta».andThen (Wiring.secondComputes F.encoding UnaryBinary.unaryEncoding)
  let first := ys.andThen (getDComputes F.encoding 0 0)
  let correct := (pairComputes first power).andThen Programs.correction
  exact congrComputes (ifComputes empty known correct) (fun x => by
    cases h : x.1 <;> simp [post,h])
theorem post_value (g : UnitInput) : post (OracleBatch.answers targetValue (pre g))=unitValue g := by
  by_cases hn : g.val.1=0
  · simp [pre,queries,metadata,known,post,OracleBatch.answers,hn,Old.one_value g hn]
  · cases hz : OldCompiler.zeroTest g with
    | true => simp [pre,queries,metadata,known,post,OracleBatch.answers,hn,hz,Old.zero_value g hz]
    | false => simpa [pre,queries,metadata,post,OracleBatch.answers,hn,hz] using Semantics.query_corrected g
theorem queries_le_one (g : UnitInput) : (queries g).length≤1 := by
  unfold queries
  split_ifs <;> simp
theorem query_words (g : UnitInput) : (queries g).map targetEncoding.encode=
    if g.val.1=0 then [] else if OldCompiler.zeroTest g then [] else [Layout.queryBits g] := by
  unfold queries
  split_ifs <;> rfl

def batch := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch preprocess postprocess targetOutput

/-- ONLY original UnitInput installation, with the programme, graph, palette,
padding count, answer codec, value equation and all bounds built internally. -/
def top : LengthControlledOracleReduction unitEncoding F.encoding
    targetEncoding F.encoding unitValue targetValue where
  reduction := {
    machine := batch.reduction.machine
    time := batch.reduction.time
    correct oracle ho g := by simpa only [post_value g] using batch.reduction.correct oracle ho g }
  targetOutput := targetOutput
  queryBound := batch.queryBound
  safeQuery := batch.safeQuery
theorem top_machine : top.reduction.machine=OracleBatch.machine preprocess.machine postprocess.machine := rfl
theorem top_time : top.reduction.time=(OracleBatch.reduction preprocess postprocess targetOutput).time := rfl
theorem top_queryBound : top.queryBound=preprocess.outputBound.bound := rfl
theorem top_answerCodec : F.encoding=WeightedMatchingInterpolation.Source.rationalField.encoding := rfl
theorem scalar_count (g : UnitInput) : Incidence.paddingCount g≤6*(unitEncoding.encode g).length :=
  Incidence.padding_input_bound g
theorem scalar_value (g : UnitInput) : targetValue (Layout.query g)=(2 : ℚ)^(Incidence.paddingCount g)*unitValue g :=
  Semantics.query_value g

theorem transcript (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput) :
    ∃ n≤top.reduction.time.eval (unitEncoding.encode g).length,
      RunsTrace top.reduction.machine oracle (top.reduction.machine.init (unitEncoding.encode g))
        (top.reduction.machine.output (F.encoding.encode (unitValue g))) n
        ((queries g).map targetEncoding.encode) := by
  have h := OracleBatch.reduction_run_trace preprocess postprocess targetOutput oracle ho g
  simp only [post_value g] at h
  simpa only [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,pre] using h

/-- Every actually reached callback has the bytes of THIS SAME generated
literal graph. Safety is obtained from its actual completed trace. -/
theorem query_origin (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (t : ℕ) (c : top.reduction.machine.Cfg)
    (hr : top.reduction.machine.run oracle (unitEncoding.encode g) t=some c)
    (hq : top.reduction.machine.IsQuery c) :
    c.stk top.reduction.machine.queryStack=Layout.queryBits g ∧
      0<g.val.1 ∧ OldCompiler.zeroTest g=false := by
  obtain ⟨n,_hn,htrace⟩ := transcript oracle ho g
  have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member htrace t c hr hq
  rw [query_words] at hm
  by_cases hn : g.val.1=0
  · simp [hn] at hm
  · cases hz : OldCompiler.zeroTest g with
    | true => simp [hn,hz] at hm
    | false => exact ⟨by simpa [hn,hz] using hm,by omega,rfl⟩
theorem query_count (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput) (t : ℕ) :
    queryCount top.reduction.machine oracle (top.reduction.machine.init (unitEncoding.encode g)) t≤1 :=
  (OracleBatch.reduction_prefix_count preprocess postprocess targetOutput oracle ho g t).trans (queries_le_one g)
theorem completed_count (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput) :
    ∃ n≤top.reduction.time.eval (unitEncoding.encode g).length,
      (fun c => c.bind (top.reduction.machine.step oracle))^[n]
        (some (top.reduction.machine.init (unitEncoding.encode g)))=
          some (top.reduction.machine.output (F.encoding.encode (unitValue g))) ∧
      queryCount top.reduction.machine oracle (top.reduction.machine.init (unitEncoding.encode g)) n=
        if g.val.1=0 then 0 else if OldCompiler.zeroTest g then 0 else 1 := by
  obtain ⟨n,hn,hr,hq,_hp⟩ := OracleBatch.reduction_query_count preprocess postprocess targetOutput oracle ho g
  refine ⟨n,hn,by simpa only [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,post_value g] using hr,?_⟩
  by_cases hz0 : g.val.1=0 <;> cases hz1 : OldCompiler.zeroTest g <;>
    simpa [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,pre,queries,hz0,hz1] using hq
theorem literal_safe_query (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (t : ℕ) (c : top.reduction.machine.Cfg)
    (hr : top.reduction.machine.run oracle (unitEncoding.encode g) t=some c)
    (hq : top.reduction.machine.IsQuery c) :
    c.stk top.reduction.machine.queryStack=targetEncoding.encode (Layout.query g) ∧
      targetEncoding.decode (c.stk top.reduction.machine.queryStack)=some (Layout.query g) ∧
      (c.stk top.reduction.machine.queryStack).length≤Layout.bitBudget (unitEncoding.encode g).length := by
  have he := (query_origin oracle ho g t c hr hq).1
  rw [he]
  exact ⟨rfl,Layout.decode_query g,Layout.bit_bound g⟩
theorem zero_queries (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (hz : OldCompiler.zeroTest g=true) (t : ℕ) :
    queryCount top.reduction.machine oracle (top.reduction.machine.init (unitEncoding.encode g)) t=0 := by
  have h := OracleBatch.reduction_prefix_count preprocess postprocess targetOutput oracle ho g t
  simpa [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,pre,queries,hz] using h
theorem empty_queries (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (hn : g.val.1=0) (t : ℕ) :
    queryCount top.reduction.machine oracle (top.reduction.machine.init (unitEncoding.encode g)) t=0 := by
  have h := OracleBatch.reduction_prefix_count preprocess postprocess targetOutput oracle ho g t
  simpa [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,pre,queries,hn] using h
theorem storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (t : ℕ) (c : top.reduction.machine.Cfg)
    (hr : top.reduction.machine.run oracle (unitEncoding.encode g) t=some c) :
    stackSize c.stk≤(unitEncoding.encode g).length+t*(top.reduction.machine.primitiveBudget+
      (top.targetOutput.bound.comp top.queryBound).eval (unitEncoding.encode g).length) :=
  top.run_stackSize_le oracle ho g t c hr
theorem storage_polynomial (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (t : ℕ) (c : top.reduction.machine.Cfg)
    (ht : t≤top.reduction.time.eval (unitEncoding.encode g).length)
    (hr : top.reduction.machine.run oracle (unitEncoding.encode g) t=some c) :
    stackSize c.stk≤top.sourceOutputPolynomial.eval (unitEncoding.encode g).length := by
  have hs := storage oracle ho g t c hr
  have hm := Nat.mul_le_mul_right (top.reduction.machine.primitiveBudget+
    (top.targetOutput.bound.comp top.queryBound).eval (unitEncoding.encode g).length) ht
  simp only [LengthControlledOracleReduction.sourceOutputPolynomial,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
  omega
theorem primitive (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput) :
    ∃ n≤top.reduction.time.eval (unitEncoding.encode g).length,
      (fun c => c.bind (top.reduction.machine.step oracle))^[n]
        (some (top.reduction.machine.init (unitEncoding.encode g)))=
          some (top.reduction.machine.output (F.encoding.encode (unitValue g))) ∧
      primitiveCount top.reduction.machine oracle (top.reduction.machine.init (unitEncoding.encode g)) n≤
        (Polynomial.C top.reduction.machine.primitiveBudget*top.reduction.time).eval
          (unitEncoding.encode g).length := by
  obtain ⟨n,hn,hr,_hq,hp⟩ := OracleBatch.reduction_query_count preprocess postprocess targetOutput oracle ho g
  exact ⟨n,hn,by simpa only [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,post_value g] using hr,hp⟩

end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Source
