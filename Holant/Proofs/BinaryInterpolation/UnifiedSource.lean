import Holant.Proofs.BinaryInterpolation.SourceTransport
import Holant.Proofs.BinaryInterpolation.SingularExtraction.Composition.CostBounds
import Holant.Complexity.EdgeSubdivision.Combinators


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.UnifiedSource
open Holant Holant.Tractable Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.Certificates.MatchingContractionClosure Holant.Projective.BoundedTorsion
set_option backward.isDefEq.respectTransparency false

/- The concrete interpolation caller with the original Γ oracle codec.
Only the answer-list field conversion is new: all queries, their order, the
mode bytecode, and the old interpolation postprocessor are reused literally. -/
namespace OriginalInterpolation
open Computability Holant.Algebraic Turing
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
open Holant.OneHot.StackProgram

variable {s : ℕ} {arity : ℕ → ℕ}
variable (C : (i : Fin s) → Signature ℂ (arity i.val))
variable (ha : ∀ i x, IsAlgebraic ℚ (C i x))
variable {D : Binary (K:=ℂ)} (M : AlgebraicSource.Macro C D)
variable (p : AlgebraicSource.Pencil M.binary)

abbrev fixedField := FieldSource.fixedField C ha M p
abbrev originalField := BinaryOriginalTarget.originalField C
abbrev originalPresentation := BinaryOriginalTarget.originalPresentation C ha
abbrev originalValue := BinaryOriginalTarget.originalValue C ha
abbrev data := FieldSource.data C ha M p
abbrev inputEncoding := FieldSource.inputEncoding (s:=s) (arity:=arity)
abbrev queryEncoding := FieldSource.targetEncoding (s:=s) (arity:=arity)
abbrev answerEncoding := OracleBatch.contextEncoding (originalPresentation C ha).encoding
  MachineCapstone.codeEncoding
abbrev outputEncoding := FieldSource.outputEncoding C ha M p
abbrev sourceValue := AlgebraicSource.CommonField.sourceValue C M.binary p

def preprocessing (r : FieldSource.Input (s:=s) (arity:=arity)) :=
  MachineCapstone.preprocessing (data C ha M p) (FieldSource.asMacroInput C M r)

def pre : Computes (inputEncoding (s:=s) (arity:=arity))
    (OracleBatch.contextEncoding (queryEncoding (s:=s) (arity:=arity)) MachineCapstone.codeEncoding)
    (preprocessing C ha M p) where
  machine := (MachineCapstone.pre (data C ha M p)).machine
  time := (MachineCapstone.pre (data C ha M p)).time
  outputs r := by
    simpa only [preprocessing,inputEncoding,queryEncoding,FieldSource.input_bytes] using
      (MachineCapstone.pre (data C ha M p)).outputs (FieldSource.asMacroInput C M r)

def targetOutput : PolynomialOutputBound
    (queryEncoding (s:=s) (arity:=arity)) (originalPresentation C ha).encoding (originalValue C ha) :=
  (BinaryOriginalTarget.originalTables C ha).outputBound (originalPresentation C ha)

theorem embedded_value (q : ExactSignatureTables.Input s 1 arity) :
    BinaryOriginalTarget.embedding C M p (originalValue C ha q) =
      AlgebraicSource.CommonField.targetValue C M.binary p q := by
  have h := TableFieldTransport.evaluate_map (originalPresentation C ha)
    (fixedField C ha M p) (BinaryOriginalTarget.embedding C M p)
    (BinaryOriginalTarget.originalTables C ha) q
  rw [BinaryOriginalTarget.mapped_tables,FieldSource.target_evaluate] at h
  exact h.symm

def liftValue (z : List (originalField C) × Code (Fin 4)) :=
  (z.1.map (BinaryOriginalTarget.embedding C M p),z.2)

/-- Actual fixed rational-matrix conversion inside a variable framed-list loop.
The code component is physically preserved by leftMapComputes. -/
def liftAnswers : Computes (answerEncoding C ha)
    (MachineCapstone.answerEncoding (F:=fixedField C ha M p)) (liftValue C M p) :=
  leftMapComputes MachineCapstone.codeEncoding
    (EdgeSubdivision.Compiler.mapComputes (originalPresentation C ha).encoding
      (fixedField C ha M p).encoding (BinaryOriginalTarget.embedding C M p)
      (FieldCodec.computes (originalPresentation C ha) (fixedField C ha M p)
        (BinaryOriginalTarget.embedding C M p).toLinearMap))

def answered (r : FieldSource.Input (s:=s) (arity:=arity)) :=
  OracleBatch.answers (originalValue C ha) (preprocessing C ha M p r)

theorem lifted_answers (r : FieldSource.Input (s:=s) (arity:=arity)) :
    liftValue C M p (answered C ha M p r) =
      MachineCapstone.answered (data C ha M p) (FieldSource.asMacroInput C M r) := by
  rw [← MachineCapstone.answered_eq]
  apply Prod.ext
  · change ((preprocessing C ha M p r).1.map (originalValue C ha)).map
        (BinaryOriginalTarget.embedding C M p) =
      (preprocessing C ha M p r).1.map
        ((FieldSource.targetTables C ha M p).evaluate (fixedField C ha M p))
    rw [List.map_map]
    apply congrArg (fun f => (preprocessing C ha M p r).1.map f)
    funext q
    rw [FieldSource.target_evaluate]
    exact embedded_value C ha M p q
  · rfl

abbrev transcriptBound := OracleBatch.decoderBound (pre C ha M p) (targetOutput C ha)

def post : BinaryCompose.Machine :=
  (liftAnswers C ha M p).machine.compose (MachineCapstone.post (data C ha M p))

def postTime : Polynomial ℕ :=
  (liftAnswers C ha M p).time.comp (transcriptBound C ha M p) +
    2*MachineCapstone.transcriptBound (data C ha M p)+2+MachineCapstone.postTime (data C ha M p)

def post_outputs (r : FieldSource.Input (s:=s) (arity:=arity)) :
    TM2OutputsInTime (post C ha M p).computer ((answerEncoding C ha).encode (answered C ha M p r))
      (some ((outputEncoding C ha M p).encode (sourceValue C M p r)))
      ((postTime C ha M p).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length) := by
  have first := (liftAnswers C ha M p).outputs (answered C ha M p r)
  rw [lifted_answers] at first
  have last := MachineCapstone.post_outputs (data C ha M p) (FieldSource.asMacroInput C M r)
  rw [FieldSource.recovery] at last
  let all := BinaryCompose.Machine.compose_correct (liftAnswers C ha M p).machine
    (MachineCapstone.post (data C ha M p)) _ _ _ _ _ first last
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  simp only [FieldSource.input_bytes] at ht
  change all.steps ≤
    (liftAnswers C ha M p).time.eval ((answerEncoding C ha).encode (answered C ha M p r)).length +
      2*(((MachineCapstone.answerEncoding (F:=fixedField C ha M p)).encode
        (MachineCapstone.answered (data C ha M p) (FieldSource.asMacroInput C M r))).length + 1) +
      (MachineCapstone.postTime (data C ha M p)).eval
        ((inputEncoding (s:=s) (arity:=arity)).encode r).length at ht
  have hi : ((answerEncoding C ha).encode (answered C ha M p r)).length ≤
      (transcriptBound C ha M p).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
    simpa only [answerEncoding,answered,transcriptBound] using
      OracleBatch.decoder_length_le (pre C ha M p) (targetOutput C ha) r
  have hc : ((MachineCapstone.answerEncoding (F:=fixedField C ha M p)).encode
      (MachineCapstone.answered (data C ha M p) (FieldSource.asMacroInput C M r))).length ≤
      (MachineCapstone.transcriptBound (data C ha M p)).eval
        ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
    simpa only [inputEncoding,FieldSource.input_bytes] using
      MachineCapstone.answered_length (data C ha M p) (FieldSource.asMacroInput C M r)
  have hf := natPolynomial_eval_mono (liftAnswers C ha M p).time hi
  simp only [postTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

abbrev machine := OracleBatch.machine (pre C ha M p).machine (post C ha M p)
def timePolynomial : Polynomial ℕ :=
  (pre C ha M p).time +
    16*((pre C ha M p).outputBound.bound+transcriptBound C ha M p+1)+postTime C ha M p

theorem execution (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (originalPresentation C ha).encoding
      (originalValue C ha) oracle) (r : FieldSource.Input (s:=s) (arity:=arity)) :
    ∃ t ≤ (timePolynomial C ha M p).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (machine C ha M p) oracle
        ((machine C ha M p).init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        ((machine C ha M p).output ((outputEncoding C ha M p).encode (sourceValue C M p r))) t
        ((preprocessing C ha M p r).1.map (queryEncoding (s:=s) (arity:=arity)).encode) := by
  have hm := OracleBatch.oracle_encoded_list oracle ho (preprocessing C ha M p r).1
  have ha' : TM2OutputsInTime (pre C ha M p).machine.computer
      ((inputEncoding (s:=s) (arity:=arity)).encode r)
      (some (OracleBatch.word ((preprocessing C ha M p r).1.map
        (queryEncoding (s:=s) (arity:=arity)).encode)
        (MachineCapstone.codeEncoding.encode (preprocessing C ha M p r).2)))
      ((pre C ha M p).time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length) := by
    simpa only [OracleBatch.context_encode] using (pre C ha M p).outputs r
  have hb := post_outputs C ha M p r
  rw [answered,OracleBatch.context_encode] at hb
  simp only [OracleBatch.answers] at hb
  have hb' : TM2OutputsInTime (post C ha M p).computer
      (OracleBatch.word (((preprocessing C ha M p r).1.map
        (queryEncoding (s:=s) (arity:=arity)).encode).map oracle)
        (MachineCapstone.codeEncoding.encode (preprocessing C ha M p r).2))
      (some ((outputEncoding C ha M p).encode (sourceValue C M p r)))
      ((postTime C ha M p).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length) := by
    rw [hm]
    exact hb
  have run := OracleBatch.run_trace (pre C ha M p).machine (post C ha M p) oracle _ _ _ _
    ha'.steps hb'.steps ha'.evals_in_steps hb'.evals_in_steps
  refine ⟨_,?_,run⟩
  have ht₁ := ha'.steps_le_m
  have ht₂ := hb'.steps_le_m
  have hp := (pre C ha M p).outputBound.length_le r
  have hd := OracleBatch.decoder_length_le (pre C ha M p) (targetOutput C ha) r
  rw [OracleBatch.context_encode] at hp
  simp only [OracleBatch.answers,OracleBatch.context_encode] at hd
  have hdq : (OracleBatch.word (((preprocessing C ha M p r).1.map
      (queryEncoding (s:=s) (arity:=arity)).encode).map oracle)
      (MachineCapstone.codeEncoding.encode (preprocessing C ha M p r).2)).length ≤
      (transcriptBound C ha M p).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
    simpa only [hm] using hd
  have hh := OracleBatch.overhead_le oracle
    ((preprocessing C ha M p r).1.map (queryEncoding (s:=s) (arity:=arity)).encode)
    (MachineCapstone.codeEncoding.encode (preprocessing C ha M p r).2)
  simp only [OracleBatch.overhead] at hh
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

def reduction : PolyTimeOracleReduction (inputEncoding (s:=s) (arity:=arity)) (outputEncoding C ha M p)
    (queryEncoding (s:=s) (arity:=arity)) (originalPresentation C ha).encoding
    (sourceValue C M p) (originalValue C ha) where
  machine := machine C ha M p
  time := timePolynomial C ha M p
  correct oracle ho r := by
    let receipt := execution C ha M p oracle ho r
    let t := Classical.choose receipt
    have ht := (Classical.choose_spec receipt).1
    have hr := (Classical.choose_spec receipt).2
    exact { steps := t, evals_in_steps := hr.run, steps_le_m := ht }

/-- Query safety comes from THIS program's completed literal transcript.
No caller supplies a reduction, query-validity proof or answer-size oracle. -/
def controlled : LengthControlledOracleReduction (inputEncoding (s:=s) (arity:=arity)) (outputEncoding C ha M p)
    (queryEncoding (s:=s) (arity:=arity)) (originalPresentation C ha).encoding
    (sourceValue C M p) (originalValue C ha) where
  reduction := reduction C ha M p
  targetOutput := targetOutput C ha
  queryBound := (pre C ha M p).outputBound.bound
  safeQuery oracle ho r t c hr hq := by
    obtain ⟨n,_,htrace⟩ := execution C ha M p oracle ho r
    have hm := TraceQueryControl.transcript_member htrace t c hr hq
    obtain ⟨q,_,he⟩ := List.mem_map.mp hm
    refine ⟨q,he.symm,?_⟩
    exact (OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le (pre C ha M p) r).1

theorem execution_certificate (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (originalPresentation C ha).encoding
      (originalValue C ha) oracle) (r : FieldSource.Input (s:=s) (arity:=arity)) :
    ∃ t ≤ (reduction C ha M p).time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      OracleBatch.RunsTrace (reduction C ha M p).machine oracle
        ((reduction C ha M p).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))
        ((reduction C ha M p).machine.output ((outputEncoding C ha M p).encode (sourceValue C M p r))) t
        ((preprocessing C ha M p r).1.map (queryEncoding (s:=s) (arity:=arity)).encode) ∧
      UniversalPairReduction.ThreeQuery.queryCount (reduction C ha M p).machine oracle
        ((reduction C ha M p).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t =
          FixedGadgetSubstitution.occurrences s r.val+1 ∧
      OracleBatch.primitiveCount (reduction C ha M p).machine oracle
        ((reduction C ha M p).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (Polynomial.C (reduction C ha M p).machine.primitiveBudget *
          (reduction C ha M p).time).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  obtain ⟨t,ht,hr⟩ := execution C ha M p oracle ho r
  refine ⟨t,ht,hr,?_,?_⟩
  · have hc := hr.count
    simpa only [reduction,List.length_map,preprocessing,MachineCapstone.preprocessing,
      EncodedBatch.preprocess,EncodedBatch.query_count,FieldSource.asMacroInput] using hc
  · exact (OracleBatch.primitiveCount_le _ _ _ _).trans (by
      simpa only [reduction,Polynomial.eval_mul,Polynomial.eval_C] using
        Nat.mul_le_mul_left (reduction C ha M p).machine.primitiveBudget ht)

/-- Every actual reachable prefix, without a supplied halt or query bound. -/
theorem encountered_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (originalPresentation C ha).encoding
      (originalValue C ha) oracle) (r : FieldSource.Input (s:=s) (arity:=arity)) (t : ℕ)
    (c : (reduction C ha M p).machine.Cfg)
    (hr : (reduction C ha M p).machine.run oracle ((inputEncoding (s:=s) (arity:=arity)).encode r) t=some c) :
    stackSize c.stk ≤ ((inputEncoding (s:=s) (arity:=arity)).encode r).length +
      t*((reduction C ha M p).machine.primitiveBudget+
        ((targetOutput C ha).bound.comp (controlled C ha M p).queryBound).eval
          ((inputEncoding (s:=s) (arity:=arity)).encode r).length) :=
  (controlled C ha M p).run_stackSize_le oracle ho r t c hr

theorem encountered_answer (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (originalPresentation C ha).encoding
      (originalValue C ha) oracle) (r : FieldSource.Input (s:=s) (arity:=arity)) (t : ℕ)
    (c : (reduction C ha M p).machine.Cfg)
    (hr : (reduction C ha M p).machine.run oracle ((inputEncoding (s:=s) (arity:=arity)).encode r) t=some c)
    (hq : (reduction C ha M p).machine.IsQuery c) :
    (oracle (c.stk (reduction C ha M p).machine.queryStack)).length ≤
      ((targetOutput C ha).bound.comp (controlled C ha M p).queryBound).eval
        ((inputEncoding (s:=s) (arity:=arity)).encode r).length :=
  (controlled C ha M p).answer_length_le oracle ho r t c hr hq

theorem bounded_prefix_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (originalPresentation C ha).encoding
      (originalValue C ha) oracle) (r : FieldSource.Input (s:=s) (arity:=arity)) (t : ℕ)
    (c : (reduction C ha M p).machine.Cfg)
    (ht : t≤(reduction C ha M p).time.eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length)
    (hr : (reduction C ha M p).machine.run oracle ((inputEncoding (s:=s) (arity:=arity)).encode r) t=some c) :
    stackSize c.stk ≤ (controlled C ha M p).sourceOutputPolynomial.eval
      ((inputEncoding (s:=s) (arity:=arity)).encode r).length := by
  have hs := encountered_storage C ha M p oracle ho r t c hr
  have hm := Nat.mul_le_mul_right ((reduction C ha M p).machine.primitiveBudget+
    ((targetOutput C ha).bound.comp (controlled C ha M p).queryBound).eval
      ((inputEncoding (s:=s) (arity:=arity)).encode r).length) ht
  simpa only [LengthControlledOracleReduction.sourceOutputPolynomial,controlled,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C] using
      hs.trans (Nat.add_le_add_left hm ((inputEncoding (s:=s) (arity:=arity)).encode r).length)

end OriginalInterpolation

namespace S
export SingularExtraction.SourceReduction
  (reduction sourceValue targetValue outputEncoding source_exact target_exact)
end S
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
abbrev gamma := Set.range (fun i : Fin s => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex))
variable (hs : ¬ CommonOneSided (gamma G))
variable (B : Binary (K:=AlgebraicComplex)) (hB : B ≠ 0)
variable (hreal : Gadget.Realizes (gamma G) .disequality (Chains.binarySignature B))

include hreal in
/-- The caller's exact ordered factorization, with its scalar retained, gives
the exact binary needed by the singular machine. This is not factor access. -/
theorem factor_realizes (u v : Bool → AlgebraicComplex) (hf : B = Matrix.vecMulVec u v) :
    Gadget.Realizes (gamma G) .disequality (SingularExtraction.outerSignature u v) := by
  rw [hf] at hreal
  exact hreal

/-- The manuscript's supplied factors are used literally; no newly normalized
pair is substituted for them. The final reduction is an existing constructed
finite program, not a premise of this source statement. -/
def given_factors_reduction (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
    (hf : B = Matrix.vecMulVec u v) : PolyTimeOracleReduction
      (SingularExtraction.SourceReduction.inputEncoding (s:=s) (arity:=arity))
      (S.outputEncoding G hs u v hu hv (factor_realizes G B hreal u v hf))
      (RawClosedNetwork.validatedEncoding s 1 arity)
      (S.outputEncoding G hs u v hu hv (factor_realizes G B hreal u v hf))
      (S.sourceValue G hs u v hu hv (factor_realizes G B hreal u v hf))
      (S.targetValue G hs u v hu hv (factor_realizes G B hreal u v hf)) :=
  S.reduction G hs u v hu hv (factor_realizes G B hreal u v hf)

include hB in
/-- A nonzero singular table itself supplies the algebraic factors, via the
existing nonzero-pivot proof. No factors or whole reductions are assumed. -/
theorem singular_case (hd : Matrix.det B = 0) :
    ∃ (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
      (hf : B = Matrix.vecMulVec u v),
      B.rank = 1 ∧ Nonempty (PolyTimeOracleReduction
        (SingularExtraction.SourceReduction.inputEncoding (s:=s) (arity:=arity))
        (S.outputEncoding G hs u v hu hv (factor_realizes G B hreal u v hf))
        (RawClosedNetwork.validatedEncoding s 1 arity)
        (S.outputEncoding G hs u v hu hv (factor_realizes G B hreal u v hf))
        (S.sourceValue G hs u v hu hv (factor_realizes G B hreal u v hf))
        (S.targetValue G hs u v hu hv (factor_realizes G B hreal u v hf))) := by
  obtain ⟨u,v,hu,hv,hf⟩ := singular_binary_factors B hB hd
  exact ⟨u,v,hu,hv,hf,singular_binary_rank B hB hd,
    ⟨given_factors_reduction G hs B hreal u v hu hv hf⟩⟩

include hB in
/-- Nonsingular and singular are the actual two binary ranks. In particular
no hidden rank-zero case remains under the source's B≠0 premise. -/
theorem binary_rank_cases :
    (Matrix.det B = 0 ∧ B.rank = 1) ∨ (Matrix.det B ≠ 0 ∧ B.rank = 2) := by
  by_cases hd : Matrix.det B = 0
  · exact Or.inl ⟨hd,singular_binary_rank B hB hd⟩
  · exact Or.inr ⟨hd,by simpa using Matrix.rank_of_det_ne_zero hd⟩

theorem transfer_nonsingular (hd : Matrix.det B ≠ 0) : Matrix.det (B*X) ≠ 0 := by
  rw [Matrix.det_mul]
  exact mul_ne_zero hd det_X_ne_zero

/-- Both interpolation modes already use the same implemented weight compiler
and actual caller. The mode equation describes their literal positive nodes. -/
theorem modes {D : Binary (K:=ℂ)} (p : AlgebraicSource.Pencil D) :
    (p.geometric = true ∧ ∀ t : ℕ, p.node t = p.rho^t) ∨
    (p.geometric = false ∧ p.L = X ∧ ∀ t : ℕ, p.node t = (t:ℂ)) := by
  cases hg : p.geometric
  · exact Or.inr ⟨rfl,p.jordan_left hg,fun t => by simp [AlgebraicSource.Pencil.node,hg]⟩
  · exact Or.inl ⟨rfl,fun t => by simp [AlgebraicSource.Pencil.node,hg]⟩

include hB hreal in
/-- The original algebraic B and direct Γ gadget are faithfully embedded for
the existing spectral capstone. Infinite order is reflected through that
embedding, so it is not an extra premise about a different matrix. -/
theorem infinite_case (hd : Matrix.det (B*X) ≠ 0) (hi : ¬ ProjectivelyFinite (B*X)) :
    ∃ M : AlgebraicSource.Macro (SourceTransport.family G) (SourceTransport.binary B),
      ∃ p : AlgebraicSource.Pencil M.binary,
        p.H ≠ 0 ∧ p.H.rank = 1 ∧ AlgebraicSource.EntriesAlgebraic p.H ∧
        ((p.geometric = true ∧ ∀ t : ℕ, p.node t = p.rho^t) ∨
          (p.geometric = false ∧ p.L = X ∧ ∀ t : ℕ, p.node t = (t:ℂ))) ∧
        Nonempty (PolyTimeOracleReduction
          (FieldSource.inputEncoding (s:=s) (arity:=arity))
          (FieldSource.outputEncoding (SourceTransport.family G) (SourceTransport.family_algebraic G) M p)
          (RawClosedNetwork.validatedEncoding s 1 arity)
          (FieldSource.outputEncoding (SourceTransport.family G) (SourceTransport.family_algebraic G) M p)
          (AlgebraicSource.CommonField.sourceValue (SourceTransport.family G) M.binary p)
          (AlgebraicSource.CommonField.targetValue (SourceTransport.family G) M.binary p)) := by
  obtain ⟨M,p,hH,hr,ha,hm⟩ := SourceCapstone.binary_interpolation
    (SourceTransport.family G) (SourceTransport.family_algebraic G)
    (SourceTransport.binary B) (SourceTransport.binary_nonzero B hB)
    (SourceTransport.transfer_det_nonzero B hd) (SourceTransport.transfer_infinite B hi)
    (SourceTransport.realizes G B hreal)
  exact ⟨M,p,hH,hr,ha,modes p,hm⟩

include hB in
/-- Full source classification. The first and final alternatives contain actual
machine terms built above. The middle alternative is precisely the finite-order
invertible regime on which Lemma 3.1 makes no extraction assertion. Retention
matches the manuscript; the constructions in fact require only two-sidedness.
Finite Γ and algebraicity are enforced by Fin s and AlgebraicComplex. -/
theorem source_capstone (_retained : Preprocessed (gamma G)) :
    (∃ (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
      (hf : B = Matrix.vecMulVec u v),
      B.rank = 1 ∧ Nonempty (PolyTimeOracleReduction
        (SingularExtraction.SourceReduction.inputEncoding (s:=s) (arity:=arity))
        (S.outputEncoding G hs u v hu hv (factor_realizes G B hreal u v hf))
        (RawClosedNetwork.validatedEncoding s 1 arity)
        (S.outputEncoding G hs u v hu hv (factor_realizes G B hreal u v hf))
        (S.sourceValue G hs u v hu hv (factor_realizes G B hreal u v hf))
        (S.targetValue G hs u v hu hv (factor_realizes G B hreal u v hf)))) ∨
    (B.rank = 2 ∧ Matrix.det (B*X) ≠ 0 ∧ ProjectivelyFinite (B*X)) ∨
    (B.rank = 2 ∧ ∃ M : AlgebraicSource.Macro (SourceTransport.family G) (SourceTransport.binary B),
      ∃ p : AlgebraicSource.Pencil M.binary,
        p.H ≠ 0 ∧ p.H.rank = 1 ∧ AlgebraicSource.EntriesAlgebraic p.H ∧
        ((p.geometric = true ∧ ∀ t : ℕ, p.node t = p.rho^t) ∨
          (p.geometric = false ∧ p.L = X ∧ ∀ t : ℕ, p.node t = (t:ℂ))) ∧
        Nonempty (PolyTimeOracleReduction
          (FieldSource.inputEncoding (s:=s) (arity:=arity))
          (FieldSource.outputEncoding (SourceTransport.family G) (SourceTransport.family_algebraic G) M p)
          (RawClosedNetwork.validatedEncoding s 1 arity)
          (FieldSource.outputEncoding (SourceTransport.family G) (SourceTransport.family_algebraic G) M p)
          (AlgebraicSource.CommonField.sourceValue (SourceTransport.family G) M.binary p)
          (AlgebraicSource.CommonField.targetValue (SourceTransport.family G) M.binary p))) := by
  rcases binary_rank_cases B hB with ⟨hd,hr⟩ | ⟨hd,hr⟩
  · exact Or.inl (singular_case G hs B hB hreal hd)
  · have ht := transfer_nonsingular B hd
    by_cases hi : ProjectivelyFinite (B*X)
    · exact Or.inr (Or.inl ⟨hr,ht,hi⟩)
    · exact Or.inr (Or.inr ⟨hr,infinite_case G B hB hreal ht hi⟩)

/-- Literal target graph bits coincide in every branch. Only fixed numerical
answer presentations differ between independently chosen fixed families. -/
theorem target_encoding_same :
    SingularExtraction.SourceReduction.queryEncoding (s:=s) (arity:=arity) =
      FieldSource.targetEncoding (s:=s) (arity:=arity) := rfl

/-- The singular oracle's field answer embeds to the exact same original Γ
complex value used by the infinite-order capstone. No codec conversion or
additional oracle call is invoked to establish this semantic identity. -/
theorem singular_target_exact (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
    (hf : B = Matrix.vecMulVec u v) (q : ExactSignatureTables.Input s 1 arity) :
    SourceTransport.inclusion
      (S.targetValue G hs u v hu hv (factor_realizes G B hreal u v hf) q : AlgebraicComplex) =
      (q.val.realize q.property (SourceTransport.family G) (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [S.target_exact]
  exact SourceTransport.closed_value G q

theorem singular_source_exact (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
    (hf : B = Matrix.vecMulVec u v)
    (r : SingularExtraction.OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    SourceTransport.inclusion
      (S.sourceValue G hs u v hu hv (factor_realizes G B hreal u v hf) r : AlgebraicComplex) =
      (r.val.realize r.property
        (SourceTransport.family (SingularExtraction.Tables.typed
          (SingularExtraction.Tables.familyTable G u v) (s+2)
          (SingularExtraction.Tables.adjoinedArity s arity 1 1)))
        (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [S.source_exact]
  exact SourceTransport.closed_value _ r

theorem infinite_target_exact
    (M : AlgebraicSource.Macro (SourceTransport.family G) (SourceTransport.binary B))
    (p : AlgebraicSource.Pencil M.binary) (q : ExactSignatureTables.Input s 1 arity) :
    (AlgebraicSource.CommonField.targetValue (SourceTransport.family G) M.binary p q : ℂ) =
      (q.val.realize q.property (SourceTransport.family G) (fun _ => Signature.disequality)).denote Fin.elim0 :=
  AlgebraicSource.CommonField.target_value_exact (SourceTransport.family G) M.binary p q

theorem infinite_source_exact
    (M : AlgebraicSource.Macro (SourceTransport.family G) (SourceTransport.binary B))
    (p : AlgebraicSource.Pencil M.binary) (r : FieldSource.Input (s:=s) (arity:=arity)) :
    (AlgebraicSource.CommonField.sourceValue (SourceTransport.family G) M.binary p r : ℂ) =
      (r.val.realize r.property
        (UniversalPairReduction.BinaryFamily.signatures (SourceTransport.family G) p.H)
        (fun _ => Signature.disequality)).denote Fin.elim0 :=
  AlgebraicSource.CommonField.source_value_exact (SourceTransport.family G) M.binary p r

namespace CS
export SingularExtraction.Composition.SourceEndpoint
  (canonical_execution canonicalPrimitive query)
export SingularExtraction.Composition.CostBounds
  (word_bounds execution_budget decoded_length embedded_length)
end CS

/-- The singular source already supplies the complete actual controlled
programme, including the canonical original Γ codec and both field conversions.
No old PolyTimeOracleReduction is promoted by an assumed control certificate. -/
def given_factors_controlled (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
    (hf : B=Matrix.vecMulVec u v) : LengthControlledOracleReduction
      (SingularExtraction.SourceReduction.inputEncoding (s:=s) (arity:=arity))
      (SingularExtraction.Composition.SourceCodec.encoding G u v)
      (RawClosedNetwork.validatedEncoding s 1 arity)
      (SingularExtraction.Composition.CanonicalOracle.encoding G)
      (SingularExtraction.Composition.SourceCodec.value G u v)
      (SingularExtraction.Composition.CanonicalOracle.value G) :=
  SingularExtraction.Composition.SourceEndpoint.canonicalControlled G hs u v hu hv
    (factor_realizes G B hreal u v hf)

include hs hB hreal in
theorem singular_controlled_case (hd : Matrix.det B=0) :
    ∃ (u v : Bool → AlgebraicComplex) (hu : u≠0) (hv : v≠0) (hf : B=Matrix.vecMulVec u v),
      B.rank=1 ∧ Nonempty (LengthControlledOracleReduction
        (SingularExtraction.SourceReduction.inputEncoding (s:=s) (arity:=arity))
        (SingularExtraction.Composition.SourceCodec.encoding G u v)
        (RawClosedNetwork.validatedEncoding s 1 arity)
        (SingularExtraction.Composition.CanonicalOracle.encoding G)
        (SingularExtraction.Composition.SourceCodec.value G u v)
        (SingularExtraction.Composition.CanonicalOracle.value G)) := by
  obtain ⟨u,v,hu,hv,hf⟩ := singular_binary_factors B hB hd
  exact ⟨u,v,hu,hv,hf,singular_binary_rank B hB hd,
    ⟨given_factors_controlled G hs B hreal u v hu hv hf⟩⟩

include hB hreal in
theorem infinite_controlled_case (hd : Matrix.det (B*X)≠0) (hi : ¬ProjectivelyFinite (B*X)) :
    ∃ M : AlgebraicSource.Macro (SourceTransport.family G) (SourceTransport.binary B),
      ∃ p : AlgebraicSource.Pencil M.binary,
        p.H≠0 ∧ p.H.rank=1 ∧ AlgebraicSource.EntriesAlgebraic p.H ∧
        ((p.geometric=true ∧ ∀t:ℕ,p.node t=p.rho^t) ∨
          (p.geometric=false ∧ p.L=X ∧ ∀t:ℕ,p.node t=(t:ℂ))) ∧
        Nonempty (LengthControlledOracleReduction
          (FieldSource.inputEncoding (s:=s) (arity:=arity))
          (FieldSource.outputEncoding (SourceTransport.family G) (SourceTransport.family_algebraic G) M p)
          (RawClosedNetwork.validatedEncoding s 1 arity)
          (SingularExtraction.Composition.CanonicalOracle.encoding G)
          (AlgebraicSource.CommonField.sourceValue (SourceTransport.family G) M.binary p)
          (SingularExtraction.Composition.CanonicalOracle.value G)) := by
  obtain ⟨M,p,hH,hr,ha,_⟩ := SourceCapstone.binary_interpolation
    (SourceTransport.family G) (SourceTransport.family_algebraic G)
    (SourceTransport.binary B) (SourceTransport.binary_nonzero B hB)
    (SourceTransport.transfer_det_nonzero B hd) (SourceTransport.transfer_infinite B hi)
    (SourceTransport.realizes G B hreal)
  exact ⟨M,p,hH,hr,ha,modes p,
    ⟨OriginalInterpolation.controlled (SourceTransport.family G) (SourceTransport.family_algebraic G) M p⟩⟩

include hs hB hreal in
/-- Unique strengthened source entry for the manuscript's two numbered items.
The singular and the two infinite-order modes have concrete controlled caller
terms with the SAME original Γ target codec. Finite invertible binaries are
retained verbatim and carry no extraction assertion. -/
theorem source_controlled_capstone (_retained : Preprocessed (gamma G)) :
    (∃ (u v : Bool → AlgebraicComplex) (hu : u≠0) (hv : v≠0) (hf : B=Matrix.vecMulVec u v),
      B.rank=1 ∧ Nonempty (LengthControlledOracleReduction
        (SingularExtraction.SourceReduction.inputEncoding (s:=s) (arity:=arity))
        (SingularExtraction.Composition.SourceCodec.encoding G u v)
        (RawClosedNetwork.validatedEncoding s 1 arity)
        (SingularExtraction.Composition.CanonicalOracle.encoding G)
        (SingularExtraction.Composition.SourceCodec.value G u v)
        (SingularExtraction.Composition.CanonicalOracle.value G))) ∨
    (B.rank=2 ∧ Matrix.det (B*X)≠0 ∧ ProjectivelyFinite (B*X)) ∨
    (B.rank=2 ∧ ∃ M : AlgebraicSource.Macro (SourceTransport.family G) (SourceTransport.binary B),
      ∃ p : AlgebraicSource.Pencil M.binary,
        p.H≠0 ∧ p.H.rank=1 ∧ AlgebraicSource.EntriesAlgebraic p.H ∧
        ((p.geometric=true ∧ ∀t:ℕ,p.node t=p.rho^t) ∨
          (p.geometric=false ∧ p.L=X ∧ ∀t:ℕ,p.node t=(t:ℂ))) ∧
        Nonempty (LengthControlledOracleReduction
          (FieldSource.inputEncoding (s:=s) (arity:=arity))
          (FieldSource.outputEncoding (SourceTransport.family G) (SourceTransport.family_algebraic G) M p)
          (RawClosedNetwork.validatedEncoding s 1 arity)
          (SingularExtraction.Composition.CanonicalOracle.encoding G)
          (AlgebraicSource.CommonField.sourceValue (SourceTransport.family G) M.binary p)
          (SingularExtraction.Composition.CanonicalOracle.value G))) := by
  rcases binary_rank_cases B hB with ⟨hd,hr⟩ | ⟨hd,hr⟩
  · exact Or.inl (singular_controlled_case G hs B hB hreal hd)
  · have ht := transfer_nonsingular B hd
    by_cases hi : ProjectivelyFinite (B*X)
    · exact Or.inr (Or.inl ⟨hr,ht,hi⟩)
    · exact Or.inr (Or.inr ⟨hr,infinite_controlled_case G B hB hreal ht hi⟩)

/-- Semantic correctness of the common canonical target. Its actual codec
conversion is liftAnswers/CanonicalOracle.decodeComputes, not this inclusion. -/
theorem controlled_target_exact (q : ExactSignatureTables.Input s 1 arity) :
    (SingularExtraction.Composition.CanonicalOracle.value G q : ℂ) =
      SourceTransport.inclusion ((q.val.realize q.property G
        (fun _ => Signature.disequality)).denote Fin.elim0) := by
  rw [Holant.LocalDrafts.MainChain.BinaryOriginalTarget.target_value_exact]
  exact (SourceTransport.closed_value G q).symm

end Holant.LocalDrafts.BinaryInterpolation.UnifiedSource
