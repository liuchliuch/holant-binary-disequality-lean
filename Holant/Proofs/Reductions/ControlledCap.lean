import Holant.Proofs.Reductions.ContextControl
import Holant.Proofs.Reductions.NativeCapReduction
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ContextCount


noncomputable section
namespace Holant.LocalDrafts.Hardness.ControlledCap
open Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution

section Context
variable {α β γ δ ε : Type}
variable {ea : Encoding α Bool} {eb : Encoding β Bool}
variable {ec : Encoding γ Bool} {ed : Encoding δ Bool} {ee : Encoding ε Bool}
variable {pre : α → γ × ε} {post : δ × ε → β} {g : γ → δ}

def controlledContext (a : Computes ea (pairEncoding ec ee) pre)
    (b : Computes (pairEncoding ed ee) eb post) (size : PolynomialOutputBound ec ed g) :
    LengthControlledOracleReduction ea eb ec ed
      (fun x => post (g (pre x).1, (pre x).2)) g where
  reduction := OracleOneQuery.Context.reduction a b size
  targetOutput := size
  queryBound := a.outputBound.bound
  safeQuery oracle _ x t c hr hq := by
    have hc := ContextControl.query_configuration a.machine b.machine oracle
      (ea.encode x) (ec.encode (pre x).1) (ee.encode (pre x).2)
      (a.outputs x).steps t c (a.outputs x).evals_in_steps hr hq
    subst c
    have hs : (ContextControl.queryCfg a.machine b.machine
        (ec.encode (pre x).1) (ee.encode (pre x).2)).stk
        (OracleOneQuery.Context.machine a.machine b.machine).queryStack =
        ec.encode (pre x).1 := by
      simp [ContextControl.queryCfg, OracleOneQuery.Context.machine,
        StackProtocol.cfg, StackProtocol.tapes3, Machine.sourceKey,
        Machine.destinationKey, Machine.temporaryKey]
    refine ⟨(pre x).1, hs, ?_⟩
    change ((ContextControl.queryCfg a.machine b.machine (ec.encode (pre x).1) (ee.encode (pre x).2)).stk
      (OracleOneQuery.Context.machine a.machine b.machine).queryStack).length ≤ _
    rw [hs]
    exact (OracleOneQuery.Context.query_context_length_le a x).1

def controlledContextOfEq (a : Computes ea (pairEncoding ec ee) pre)
    (b : Computes (pairEncoding ed ee) eb post) (size : PolynomialOutputBound ec ed g)
    (f : α → β) (heq : ∀ x, f x = post (g (pre x).1, (pre x).2)) :
    LengthControlledOracleReduction ea eb ec ed f g := by
  have hf : f = fun x => post (g (pre x).1, (pre x).2) := funext heq
  subst f
  exact controlledContext a b size

theorem controlledContextOfEq_time (a : Computes ea (pairEncoding ec ee) pre)
    (b : Computes (pairEncoding ed ee) eb post) (size : PolynomialOutputBound ec ed g)
    (f : α → β) (heq : ∀ x, f x = post (g (pre x).1, (pre x).2)) :
    (controlledContextOfEq a b size f heq).reduction.time =
      (OracleOneQuery.Context.reduction a b size).time := by
  have hf : f = fun x => post (g (pre x).1, (pre x).2) := funext heq
  subst f
  rfl

theorem controlledContextOfEq_machine (a : Computes ea (pairEncoding ec ee) pre)
    (b : Computes (pairEncoding ed ee) eb post) (size : PolynomialOutputBound ec ed g)
    (f : α → β) (heq : ∀ x, f x = post (g (pre x).1, (pre x).2)) :
    (controlledContextOfEq a b size f heq).reduction.machine =
      (controlledContext a b size).reduction.machine := by
  have hf : f = fun x => post (g (pre x).1, (pre x).2) := funext heq
  subst f
  rfl

/-- Counts executed oracle transitions on arbitrary prefixes, rather than just
counting query labels in the program text. Reuses the existing potential proof. -/
theorem controlledContext_atMostOne (a : Computes ea (pairEncoding ec ee) pre)
    (b : Computes (pairEncoding ed ee) eb post) (size : PolynomialOutputBound ec ed g) :
    UniversalPairReduction.ThreeQuery.AtMostQueries
      (controlledContext a b size).reduction.machine 1 :=
  UniversalPairReduction.SmoothingCompiler.ContextCount.atMostOne a.machine b.machine
end Context

section Substitution
variable {K : Type} [Field K] [Algebra ℚ K]
variable {d sourceCount s e : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d) (templates : ℕ → Template)
variable (hg : ∀ i < sourceCount, (templates i).WellFormed s e arity)
variable (T : ExactSignatureTables d s e arity)
variable (source : (i : Fin sourceCount) → Signature (Fin d → ℚ) (sourceArity templates i.val))

/-- Generic graph substitution: the hypothesis is a local, finite gadget
identity. It is derived from the factorization below for the extraction caller. -/
def controlledSubstitution (label : ℕ) (scale : K) (hscale : scale ≠ 0)
    (hdenote : ∀ i : Fin sourceCount,
      ((templates i.val).network (hg i.val i.isLt)
        (fun j x => F.decode (T.vertex j x))
        (fun j u v => F.decode (T.edge j u v))).denote =
        (if i.val = label then scale else 1) • (fun x => F.decode (source i x))) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding sourceCount e (sourceArity templates)) F.encoding
      (RawClosedNetwork.validatedEncoding s e arity) F.encoding
      ((sourceTables templates T source).evaluate F) (T.evaluate F) := by
  let pre := Compiler.withOccurrencesComputes sourceCount e (sourceArity templates)
    templates s arity (compilerHypotheses templates hg) label
  apply controlledContextOfEq pre (ScalarPower.correction F scale) (T.outputBound F)
    ((sourceTables templates T source).evaluate F)
  intro r
  have hp := replacement_scale_power templates r.val r.property hg
    (fun i x => F.decode (source i x)) (fun j x => F.decode (T.vertex j x))
    (fun j u v => F.decode (T.edge j u v)) label scale hdenote
  change T.evaluate F (Compiler.value sourceCount e (sourceArity templates) templates s arity
      (compilerHypotheses templates hg) r) =
    scale ^ occurrences label r.val * (sourceTables templates T source).evaluate F r at hp
  change (sourceTables templates T source).evaluate F r =
    T.evaluate F (Compiler.value sourceCount e (sourceArity templates) templates s arity
      (compilerHypotheses templates hg) r) * (scale⁻¹) ^ occurrences label r.val
  rw [hp, ScalarPower.cancel_scale_power scale _ hscale]

variable (g : Template) (hg : g.WellFormed s e arity) (scale : K)

/-- The scalar power, input count, valid query bytes, and query-length control
all belong to the same concrete caller; no separate safety certificate is input. -/
def scaledAdjoin (hscale : scale ≠ 0) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (s+1) e (sourceArity (Adjoin.templates s arity g))) F.encoding
      (RawClosedNetwork.validatedEncoding s e arity) F.encoding
      ((sourceTables (Adjoin.templates s arity g) T
        (ScaledAdjoin.coordinates F T g hg scale)).evaluate F) (T.evaluate F) := by
  apply controlledSubstitution F (Adjoin.templates s arity g) (Adjoin.wellFormed g hg)
    T (ScaledAdjoin.coordinates F T g hg scale) s scale hscale
  intro i
  funext x
  change ((Adjoin.templates s arity g i.val).network _
      (fun j y => F.decode (T.vertex j y))
      (fun j u v => F.decode (T.edge j u v))).denote x =
    (if i.val = s then scale else 1) * F.decode (ScaledAdjoin.coordinates F T g hg scale i x)
  unfold ScaledAdjoin.coordinates ScaledAdjoin.rescale
  rw [LinearEquiv.apply_symm_apply]
  dsimp only [Adjoin.coordinates]
  rw [decode_templateCoordinates]
  have hn : (if i.val = s then scale else 1) ≠ 0 := by split_ifs <;> simp_all
  field_simp
end Substitution

section Extraction
open NativeCap NativeCapReduction ExactSignatureTables
variable {L : Type} [Field L] [Algebra ℚ L] {s n : ℕ} {arity : ℕ → ℕ}
variable (coeff : CoefficientIndex s 1 arity → L)
variable (halg : ∀ i, IsAlgebraic ℚ (coeff i))
variable (j : Fin s) (hj : arity j.val = n + 2)
variable (a : Signature L n) (haalg : ∀ x, IsAlgebraic ℚ (a x))
variable (p : Fin n → Bool)

abbrev fieldPresentation := AlgebraicProjectiveAdjoin.presentation coeff halg (capTemplate coeff j hj) a haalg
abbrev targetTables := AlgebraicProjectiveAdjoin.originalTables coeff halg (capTemplate coeff j hj) a haalg
abbrev scale := AlgebraicProjectiveAdjoin.scaleAt coeff halg (capTemplate coeff j hj)
  (macroValid coeff j hj) a haalg p

abbrev SourceEncoding := RawClosedNetwork.validatedEncoding (s+1) 1
  (sourceArity (Adjoin.templates s arity (capTemplate coeff j hj)))
abbrev TargetEncoding := RawClosedNetwork.validatedEncoding s 1 arity
abbrev AnswerEncoding := (fieldPresentation coeff halg j hj a haalg).encoding
abbrev sourceValue :=
  (sourceTables (Adjoin.templates s arity (capTemplate coeff j hj))
    (targetTables coeff halg j hj a haalg)
    (ScaledAdjoin.coordinates (fieldPresentation coeff halg j hj a haalg)
      (targetTables coeff halg j hj a haalg) (capTemplate coeff j hj) (macroValid coeff j hj)
      (scale coeff halg j hj a haalg p))).evaluate (fieldPresentation coeff halg j hj a haalg)
abbrev targetValue := (targetTables coeff halg j hj a haalg).evaluate
  (fieldPresentation coeff halg j hj a haalg)

/-- The represented source answer is the original graph sum with the normalized
factor at the appended label. NativeCapReduction.source_family_exact identifies
that family with Gamma union {a}, including coincident labels. -/
theorem source_value_exact
    (r : Input (s+1) 1 (sourceArity (Adjoin.templates s arity (capTemplate coeff j hj)))) :
    ((sourceValue coeff halg j hj a haalg p r :
      familyField (AlgebraicProjectiveAdjoin.values coeff (capTemplate coeff j hj) a)) : L) =
      (r.val.realize r.property
        (PresentedScaledFamily.ambientSource
          (AlgebraicProjectiveAdjoin.values coeff (capTemplate coeff j hj) a) Sum.inl
          (capTemplate coeff j hj) (macroValid coeff j hj) (scale coeff halg j hj a haalg p))
        (fun i u v => coeff (.inr (i,u,v)))).denote Fin.elim0 :=
  PresentedScaledFamily.source_value_exact
    (AlgebraicProjectiveAdjoin.values coeff (capTemplate coeff j hj) a)
    (AlgebraicProjectiveAdjoin.values_algebraic coeff halg (capTemplate coeff j hj) a haalg)
    Sum.inl (capTemplate coeff j hj) (macroValid coeff j hj) (scale coeff halg j hj a haalg p) r

def controlledExtraction
    (hnative : ∀ (i : Fin 1) u v, coeff (.inr (i,u,v)) = Signature.disequality u v)
    (b : Bool → Bool → L) (hf : retained coeff j hj = frontProduct b a)
    (hc : capScalar b ≠ 0) (hp : a p ≠ 0) :
    LengthControlledOracleReduction
      (SourceEncoding coeff j hj) (AnswerEncoding coeff halg j hj a haalg)
      (TargetEncoding (s:=s) (arity:=arity)) (AnswerEncoding coeff halg j hj a haalg)
      (sourceValue coeff halg j hj a haalg p) (targetValue coeff halg j hj a haalg) :=
  scaledAdjoin (fieldPresentation coeff halg j hj a haalg)
    (targetTables coeff halg j hj a haalg) (capTemplate coeff j hj) (macroValid coeff j hj)
    (scale coeff halg j hj a haalg p)
    (AlgebraicProjectiveAdjoin.scaleAt_ne_zero coeff halg (capTemplate coeff j hj)
      (macroValid coeff j hj) a haalg (capScalar b) hc
      (macro_exact coeff j hj hnative b a hf) p hp)

/-- Integration only: r is an already implemented downstream reduction over
the identical target codec. This constructs the actual inlined machine; it
does not assert existence of r or of a hardness base case. -/
def extractionThen {ε ζ : Type} {ee : Encoding ε Bool} {ef : Encoding ζ Bool} {f : ε → ζ}
    (hnative : ∀ (i : Fin 1) u v, coeff (.inr (i,u,v)) = Signature.disequality u v)
    (b : Bool → Bool → L) (hf : retained coeff j hj = frontProduct b a)
    (hc : capScalar b ≠ 0) (hp : a p ≠ 0)
    (r : PolyTimeOracleReduction (TargetEncoding (s:=s) (arity:=arity))
      (AnswerEncoding coeff halg j hj a haalg) ee ef
      (targetValue coeff halg j hj a haalg) f) :
    PolyTimeOracleReduction (SourceEncoding coeff j hj)
      (AnswerEncoding coeff halg j hj a haalg) ee ef (sourceValue coeff halg j hj a haalg p) f :=
  (controlledExtraction coeff halg j hj a haalg p hnative b hf hc hp).compose r
end Extraction

end Holant.LocalDrafts.Hardness.ControlledCap
