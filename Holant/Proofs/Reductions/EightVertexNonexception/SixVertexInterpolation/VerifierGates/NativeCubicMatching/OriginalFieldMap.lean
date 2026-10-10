import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.Source
import Holant.OneHot.ArithmeticSize


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.OriginalFieldMap
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open UniversalPairReduction.ThreeQuery Holant.Complexity.BinaryInterpolation
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.CountingHardness.VerifierCompiler.Stateful.CapacityFrontend
open WeightedMatchingInterpolation
open Holant.Complexity.OracleBatch
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {L : Type} [Field L] [Algebra ℚ L] {d : ℕ} (F : FixedField L d)

def ONE_L : Signature L 3 := fun x =>
  if (OldTree.bit (x 0)+OldTree.bit (x 1)+OldTree.bit (x 2)==1) then 1 else 0
def TWO_L : Signature L 3 := fun x => ONE_L (fun i => !x i)
def paletteL (i : Fin 2) : Signature L (arity i.val) := if i.val=0 then ONE_L else TWO_L
def edgeL (_ : Fin 1) : Kernel L := Signature.disequality
abbrev TargetInput := Semantics.TargetInput
abbrev targetEncoding := Semantics.targetEncoding
def targetValue (r : TargetInput) : L := (r.val.realize r.property paletteL edgeL).denote Fin.elim0
def unitValueL (g : UnitInput) : L := algebraMap ℚ L (unitValue g)
theorem unitValueL_count (g : UnitInput) : unitValueL g=(unitCount g : L) := by
  simp [unitValueL,unitValue]

theorem one_map (x : Fin 3 → Bool) : algebraMap ℚ L (ONE x)=ONE_L x := by
  unfold ONE ONE_L
  split_ifs <;> simp
theorem two_map (x : Fin 3 → Bool) : algebraMap ℚ L (TWO x)=TWO_L x := one_map (fun i => !x i)
theorem palette_map (i : Fin 2) (x : Fin (arity i.val) → Bool) :
    algebraMap ℚ L (palette i x)=paletteL i x := by
  fin_cases i
  · simpa [palette,paletteL] using one_map (L := L) x
  · simpa [palette,paletteL] using two_map (L := L) x
theorem edge_map (i : Fin 1) (a b : Bool) : algebraMap ℚ L (edge i a b)=edgeL i a b := by
  cases a <;> cases b <;> simp [edge,edgeL,Signature.disequality]

/-- The entire SAME graph tensor is transported, including both actual
self-loop ends, parallel occurrences and the original ordered ports. -/
theorem target_map (r : TargetInput) : algebraMap ℚ L (Semantics.targetValue r)=targetValue r := by
  change algebraMap ℚ L (∑ z : (Fin r.val.edges.length × Bool) → Bool,
      (∏ v : Fin r.val.vertices.length,palette (r.val.signatureLabel r.property v)
        ((r.val.shape r.property).assignment Fin.elim0 z v)) *
      ∏ e : Fin r.val.edges.length,edge (r.val.edgeLabel r.property e) (z (e,false)) (z (e,true))) =
    ∑ z : (Fin r.val.edges.length × Bool) → Bool,
      (∏ v : Fin r.val.vertices.length,paletteL (r.val.signatureLabel r.property v)
        ((r.val.shape r.property).assignment Fin.elim0 z v)) *
      ∏ e : Fin r.val.edges.length,edgeL (r.val.edgeLabel r.property e) (z (e,false)) (z (e,true))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_mul,map_prod,map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    exact palette_map _ _
  · apply Finset.prod_congr rfl
    intro e _
    exact edge_map _ _ _
theorem query_value (g : UnitInput) :
    targetValue (Layout.query g)=(2 : L)^(Incidence.paddingCount g)*unitValueL g := by
  rw [←target_map,Semantics.query_value]
  simp only [unitValueL,map_mul,map_pow,map_ofNat]
theorem two_ne_zero : (2 : L) ≠ 0 := by
  intro h
  have hm : algebraMap ℚ L ((2 : ℚ)*(2 : ℚ)⁻¹) = (1 : L) := by norm_num
  rw [map_mul] at hm
  have hz : (0 : L)=1 := by simpa [h] using hm
  exact zero_ne_one hz
theorem query_corrected (g : UnitInput) :
    targetValue (Layout.query g)*((2 : L)⁻¹)^(Incidence.paddingCount g)=unitValueL g := by
  rw [query_value]
  exact ScalarPower.cancel_scale_power 2 _ two_ne_zero _
theorem empty_value (g : UnitInput) (hg : g.val.1=0) : unitValueL (L:=L) g=1 := by
  simp [unitValueL,Source.Old.one_value g hg]
theorem isolated_value (g : UnitInput) (hg : OldCompiler.zeroTest g=true) : unitValueL (L:=L) g=0 := by
  simp [unitValueL,Source.Old.zero_value g hg]

/-- An answer bound in the ORIGINAL basis; no one-coordinate replacement
or caller-supplied answer-size promise is used. -/
def unitCoefficients : Fin 1 → Fin d → ℚ := fun _ => F.unitCode
theorem count_bound (n Y : ℕ) (hn : n≤2^Y) :
    Holant.OneHot.ArithmeticSize.Bound (fun i => F.decode (unitCoefficients F i)) Y (n : L) := by
  refine ⟨n,fun _ _ => 0,hn,?_⟩
  simp [unitCoefficients]
theorem target_count (r : TargetInput) : ∃ n : ℕ,n≤2^(2*r.val.edges.length) ∧ targetValue r=(n : L) := by
  obtain ⟨n,hn,hv⟩ := Source.target_count r
  change Semantics.targetValue r=(n : ℚ) at hv
  refine ⟨n,hn,?_⟩
  rw [←target_map,hv]
  simp
def targetOutput : PolynomialOutputBound targetEncoding F.encoding targetValue where
  bound := (RingFormulaMachine.widthPolynomial F (unitCoefficients F)).comp (2*Polynomial.X)
  length_le r := by
    obtain ⟨n,hn,hv⟩ := target_count (L := L) r
    rw [hv]
    have he : r.val.edges.length≤(targetEncoding.encode r).length := by
      have h := r.val.counts_le_encoded_length
      change r.val.edges.length≤(RawClosedNetwork.encoding.encode r.val).length
      omega
    have hpow : n≤2^(2*(targetEncoding.encode r).length) :=
      hn.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 he))
    have h := (count_bound F n (2*(targetEncoding.encode r).length) hpow).encoded_length_le F (unitCoefficients F)
    simpa only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,RingFormulaMachine.width_eval] using h

/-- The fixed inverse is produced from the ORIGINAL unit coordinates by a
fixed rational half; no semantic field-inversion service is used at runtime. -/
def inverseTwoCode : Fin d → ℚ := (2 : ℚ)⁻¹ • F.unitCode
theorem inverseTwo_spec : F.decode (inverseTwoCode F)=(2 : L)⁻¹ := by
  unfold inverseTwoCode
  rw [map_smul,F.decode_unit]
  simp [Algebra.smul_def]
theorem inverseTwo_coordinates : F.decode.symm ((2 : L)⁻¹)=inverseTwoCode F := by
  apply F.decode_injective
  simp only [F.decode.apply_symm_apply,inverseTwo_spec]
theorem inverseTwo_bytes : F.encoding.encode ((2 : L)⁻¹)=(vectorEncoding d).encode (inverseTwoCode F) := by
  rw [←inverseTwo_spec,F.encoding_decode]
def correction := ScalarPower.correction F (2 : L)
def correctedOutput (g : UnitInput) : TM2OutputsInTime (correction F).machine.computer
    ((pairEncoding F.encoding UnaryBinary.unaryEncoding).encode
      (targetValue (Layout.query g),Incidence.paddingCount g))
    (some (F.encoding.encode (unitValueL g)))
    ((correction F).time.eval ((pairEncoding F.encoding UnaryBinary.unaryEncoding).encode
      (targetValue (Layout.query g),Incidence.paddingCount g)).length) := by
  rw [query_value]
  exact ScalarPower.correct_answer F 2 (unitValueL g) two_ne_zero (Incidence.paddingCount g)
theorem correction_primitive (y : L) (P : ℕ) :
    primitiveCost (correction F).machine ((correction F).outputs (y,P)).steps
      (some (initList (correction F).machine.computer
        ((pairEncoding F.encoding UnaryBinary.unaryEncoding).encode (y,P))))≤
      (primitivePolynomial (correction F)).eval
        ((pairEncoding F.encoding UnaryBinary.unaryEncoding).encode (y,P)).length :=
  computes_primitive_cost (correction F) (y,P)

abbrev queries := Source.queries
def known (g : UnitInput) : L := if g.val.1=0 then 1 else 0
def metadataEncoding := pairEncoding F.encoding UnaryBinary.unaryEncoding
def metadata (g : UnitInput) : L × ℕ := (known g,Incidence.paddingCount g)
def pre (g : UnitInput) : List TargetInput × (L × ℕ) := (queries g,metadata g)
def knownComputes : Computes unitEncoding F.encoding known :=
  congrComputes (ifComputes Source.emptyTest (constantComputes unitEncoding F.encoding 1)
    (constantComputes unitEncoding F.encoding 0)) (fun _ => by simp [known])
def preprocess : Computes unitEncoding (OracleBatch.contextEncoding targetEncoding (metadataEncoding F)) pre :=
  pairComputes Source.queryList (pairComputes (knownComputes F) Programs.paddingCount)
def answerEncoding := OracleBatch.contextEncoding F.encoding (metadataEncoding F)
def post (x : List L × (L × ℕ)) : L :=
  if x.1=[] then x.2.1 else x.1.getD 0 0*((2 : L)⁻¹)^x.2.2
def postprocess : Computes (answerEncoding F) F.encoding post := by
  let ys := Wiring.firstComputes (framedListEncoding F.encoding) (metadataEncoding F)
  let «meta» := Wiring.secondComputes (framedListEncoding F.encoding) (metadataEncoding F)
  let len := ys.andThen (WireLists.lengthComputes F.encoding)
  let empty := (pairComputes len (constantComputes (answerEncoding F) UnaryBinary.unaryEncoding 0)).andThen
    (equalComputes UnaryBinary.unaryEncoding)
  let value := «meta».andThen (Wiring.firstComputes F.encoding UnaryBinary.unaryEncoding)
  let power := «meta».andThen (Wiring.secondComputes F.encoding UnaryBinary.unaryEncoding)
  let first := ys.andThen (getDComputes F.encoding 0 0)
  let correct := (pairComputes first power).andThen (correction F)
  exact congrComputes (ifComputes empty value correct) (fun x => by cases h : x.1 <;> simp [post,h])
theorem post_value (g : UnitInput) : post (OracleBatch.answers targetValue (pre g))=unitValueL (L:=L) g := by
  by_cases hn : g.val.1=0
  · simp [pre,queries,Source.queries,metadata,known,post,OracleBatch.answers,hn,empty_value g hn]
  · cases hz : OldCompiler.zeroTest g with
    | true => simp [pre,queries,Source.queries,metadata,known,post,OracleBatch.answers,hn,hz,isolated_value g hz]
    | false => simpa [pre,queries,Source.queries,metadata,post,OracleBatch.answers,hn,hz] using query_corrected (L := L) g

def batch := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch
  (preprocess F) (postprocess F) (targetOutput F)
def top : LengthControlledOracleReduction unitEncoding F.encoding targetEncoding F.encoding unitValueL targetValue where
  reduction := {
    machine := (batch F).reduction.machine
    time := (batch F).reduction.time
    correct oracle ho g := by simpa only [post_value (L := L) g] using (batch F).reduction.correct oracle ho g }
  targetOutput := targetOutput F
  queryBound := (batch F).queryBound
  safeQuery := (batch F).safeQuery
theorem original_codec (v : Fin d → ℚ) : F.encoding.encode (F.decode v)=(vectorEncoding d).encode v :=
  F.encoding_decode v
theorem original_answer_bytes (y : L) : F.encoding.encode y=(vectorEncoding d).encode (F.decode.symm y) := by
  simpa using original_codec F (F.decode.symm y)
theorem top_targetOutput : (top F).targetOutput.bound=(targetOutput F).bound := rfl
theorem top_machine : (top F).reduction.machine=OracleBatch.machine (preprocess F).machine (postprocess F).machine := rfl
theorem top_time : (top F).reduction.time=(OracleBatch.reduction (preprocess F) (postprocess F) (targetOutput F)).time := rfl
theorem top_queryBound : (top F).queryBound=(preprocess F).outputBound.bound := rfl
theorem query_bytes (g : UnitInput) : (queries g).map targetEncoding.encode=
    if g.val.1=0 then [] else if OldCompiler.zeroTest g then [] else [Layout.queryBits g] := Source.query_words g
theorem query_renderer (g : UnitInput) : Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Programs.RunsExactly Renderer.Code.computes.machine.computer.step
    (initList Renderer.Code.computes.machine.computer (unitEncoding.encode g))
    (haltList Renderer.Code.computes.machine.computer (Layout.queryBits g)) (Renderer.Code.computes.outputs g).steps :=
  Renderer.Code.query_execution g
theorem padding_bound (g : UnitInput) : Incidence.paddingCount g≤6*(unitEncoding.encode g).length := Source.scalar_count g

theorem transcript (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput) :
    ∃ n≤(top F).reduction.time.eval (unitEncoding.encode g).length,
      RunsTrace (top F).reduction.machine oracle ((top F).reduction.machine.init (unitEncoding.encode g))
        ((top F).reduction.machine.output (F.encoding.encode (unitValueL g))) n
        ((queries g).map targetEncoding.encode) := by
  have h := OracleBatch.reduction_run_trace (preprocess F) (postprocess F) (targetOutput F) oracle ho g
  simp only [post_value (L := L) g] at h
  simpa only [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,pre] using h
theorem query_origin (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (t : ℕ) (c : (top F).reduction.machine.Cfg)
    (hr : (top F).reduction.machine.run oracle (unitEncoding.encode g) t=some c)
    (hq : (top F).reduction.machine.IsQuery c) :
    c.stk (top F).reduction.machine.queryStack=Layout.queryBits g ∧
      0<g.val.1 ∧ OldCompiler.zeroTest g=false := by
  obtain ⟨n,hn,htrace⟩ := transcript F oracle ho g
  have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member htrace t c hr hq
  rw [query_bytes] at hm
  by_cases hn : g.val.1=0
  · simp [hn] at hm
  · cases hz : OldCompiler.zeroTest g with
    | true => simp [hn,hz] at hm
    | false => exact ⟨by simpa [hn,hz] using hm,by omega,rfl⟩
theorem query_count (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput) (t : ℕ) :
    queryCount (top F).reduction.machine oracle ((top F).reduction.machine.init (unitEncoding.encode g)) t≤1 :=
  (OracleBatch.reduction_prefix_count (preprocess F) (postprocess F) (targetOutput F) oracle ho g t).trans (Source.queries_le_one g)
theorem completed_count (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput) :
    ∃ n≤(top F).reduction.time.eval (unitEncoding.encode g).length,
      (fun c => c.bind ((top F).reduction.machine.step oracle))^[n]
        (some ((top F).reduction.machine.init (unitEncoding.encode g)))=
          some ((top F).reduction.machine.output (F.encoding.encode (unitValueL g))) ∧
      queryCount (top F).reduction.machine oracle ((top F).reduction.machine.init (unitEncoding.encode g)) n=
        if g.val.1=0 then 0 else if OldCompiler.zeroTest g then 0 else 1 := by
  obtain ⟨n,hn,hr,hq,hp⟩ := OracleBatch.reduction_query_count (preprocess F) (postprocess F) (targetOutput F) oracle ho g
  refine ⟨n,hn,by simpa only [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,post_value (L := L) g] using hr,?_⟩
  by_cases hz0 : g.val.1=0 <;> cases hz1 : OldCompiler.zeroTest g <;>
    simpa [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,pre,queries,Source.queries,hz0,hz1] using hq
theorem literal_safe_query (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (t : ℕ) (c : (top F).reduction.machine.Cfg)
    (hr : (top F).reduction.machine.run oracle (unitEncoding.encode g) t=some c)
    (hq : (top F).reduction.machine.IsQuery c) :
    c.stk (top F).reduction.machine.queryStack=targetEncoding.encode (Layout.query g) ∧
      targetEncoding.decode (c.stk (top F).reduction.machine.queryStack)=some (Layout.query g) ∧
      (c.stk (top F).reduction.machine.queryStack).length≤Layout.bitBudget (unitEncoding.encode g).length := by
  have he := (query_origin F oracle ho g t c hr hq).1
  rw [he]
  exact ⟨rfl,Layout.decode_query g,Layout.bit_bound g⟩
theorem answer_bytes (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (t : ℕ) (c : (top F).reduction.machine.Cfg)
    (hr : (top F).reduction.machine.run oracle (unitEncoding.encode g) t=some c)
    (hq : (top F).reduction.machine.IsQuery c) :
    (oracle (c.stk (top F).reduction.machine.queryStack)).length≤
      ((top F).targetOutput.bound.comp (top F).queryBound).eval (unitEncoding.encode g).length :=
  (top F).answer_length_le oracle ho g t c hr hq
theorem empty_queries (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput) (hg : g.val.1=0) (t : ℕ) :
    queryCount (top F).reduction.machine oracle ((top F).reduction.machine.init (unitEncoding.encode g)) t=0 := by
  have h := OracleBatch.reduction_prefix_count (preprocess F) (postprocess F) (targetOutput F) oracle ho g t
  simpa [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,pre,queries,Source.queries,hg] using h
theorem isolated_queries (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (hg : OldCompiler.zeroTest g=true) (t : ℕ) :
    queryCount (top F).reduction.machine oracle ((top F).reduction.machine.init (unitEncoding.encode g)) t=0 := by
  have h := OracleBatch.reduction_prefix_count (preprocess F) (postprocess F) (targetOutput F) oracle ho g t
  simpa [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,pre,queries,Source.queries,hg] using h
theorem storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (t : ℕ) (c : (top F).reduction.machine.Cfg)
    (hr : (top F).reduction.machine.run oracle (unitEncoding.encode g) t=some c) :
    stackSize c.stk≤(unitEncoding.encode g).length+t*((top F).reduction.machine.primitiveBudget+
      ((top F).targetOutput.bound.comp (top F).queryBound).eval (unitEncoding.encode g).length) :=
  (top F).run_stackSize_le oracle ho g t c hr
theorem storage_polynomial (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput)
    (t : ℕ) (c : (top F).reduction.machine.Cfg)
    (ht : t≤(top F).reduction.time.eval (unitEncoding.encode g).length)
    (hr : (top F).reduction.machine.run oracle (unitEncoding.encode g) t=some c) :
    stackSize c.stk≤(top F).sourceOutputPolynomial.eval (unitEncoding.encode g).length := by
  have hs := storage F oracle ho g t c hr
  have hm := Nat.mul_le_mul_right ((top F).reduction.machine.primitiveBudget+
    ((top F).targetOutput.bound.comp (top F).queryBound).eval (unitEncoding.encode g).length) ht
  simp only [LengthControlledOracleReduction.sourceOutputPolynomial,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
  omega
theorem output_bytes (g : UnitInput) : (F.encoding.encode (unitValueL g)).length≤
    (top F).sourceOutputPolynomial.eval (unitEncoding.encode g).length := (top F).source_output_length_le g
theorem primitive (oracle : List Bool → List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding targetValue oracle) (g : UnitInput) :
    ∃ n≤(top F).reduction.time.eval (unitEncoding.encode g).length,
      (fun c => c.bind ((top F).reduction.machine.step oracle))^[n]
        (some ((top F).reduction.machine.init (unitEncoding.encode g)))=
          some ((top F).reduction.machine.output (F.encoding.encode (unitValueL g))) ∧
      primitiveCount (top F).reduction.machine oracle ((top F).reduction.machine.init (unitEncoding.encode g)) n≤
        (Polynomial.C (top F).reduction.machine.primitiveBudget*(top F).reduction.time).eval (unitEncoding.encode g).length := by
  obtain ⟨n,hn,hr,hq,hp⟩ := OracleBatch.reduction_query_count (preprocess F) (postprocess F) (targetOutput F) oracle ho g
  exact ⟨n,hn,by simpa only [top,batch,Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,post_value (L := L) g] using hr,hp⟩

end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.NativeCubicMatching.OriginalFieldMap
