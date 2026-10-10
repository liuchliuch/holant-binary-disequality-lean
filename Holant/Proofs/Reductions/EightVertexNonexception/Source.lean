import Holant.Proofs.Reductions.EightVertexNonexception.NativeChain
import Holant.Proofs.Reductions.EightVertexNonexception.BranchTest
import Holant.Proofs.Reductions.EightVertexNonexception.SparseExclusions
import Holant.Complexity.FixedGadgetSubstitution.OriginalFamily
import Holant.Tractable.CommonTransform


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {L : Type} [Field L] [Algebra ℚ L]

def coefficient (M : Signature L 4) :
    ExactSignatureTables.CoefficientIndex 1 1 (fun _ => 4) → L
  | .inl ⟨_,t⟩ => M t
  | .inr (_,a,b) => Signature.disequality a b

theorem coefficient_algebraic (M : Signature L 4)
    (halg : ∀ t, IsAlgebraic ℚ (M t)) :
    ∀ c, IsAlgebraic ℚ (coefficient M c) := by
  intro c
  cases c with
  | inl c => exact halg c.2
  | inr c =>
    rcases c with ⟨i,a,b⟩
    cases a <;> cases b <;> first | exact isAlgebraic_zero | exact isAlgebraic_one

abbrev field (M : Signature L 4) := familyField (coefficient M)
abbrev presentation (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) :=
  familyPresentation (coefficient M) (coefficient_algebraic M halg)
abbrev tables (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) :=
  OriginalFamily.tables (coefficient M) (coefficient_algebraic M halg)

/-- The new macro has the literal original-M/native-X denotation in L. -/
theorem ambient_macro (M : Signature L 4) :
    (OriginalFamily.ambientMacro (coefficient M) chainTemplate
      chainTemplate_wellFormed).denote = (nativeChain M).denote :=
  chainTemplate_denote M

def fieldSignature (M : Signature L 4) : Signature (field M) 4 := fun t =>
  fieldCoefficient (coefficient M) (.inl ⟨0,t⟩)

theorem fieldSignature_value (M : Signature L 4) (t : Word) :
    ((fieldSignature M t : field M) : L) = M t := rfl

theorem fieldSignature_eq_zero (M : Signature L 4) (t : Word) :
    fieldSignature M t = 0 ↔ M t = 0 := by
  constructor
  · intro h
    have hv := congrArg (fun k : field M => (k : L)) h
    change M t = 0 at hv
    exact hv
  · intro h
    apply Subtype.ext
    exact h

/-- The test reads exactly the original field coefficients, with no supplied
branch certificate, extension field, rescaling or alternate encoding. -/
def branch (M : Signature L 4) : Bool :=
  BranchTest.test (BranchTest.entriesList (fieldSignature M))

theorem branch_correct (M : Signature L 4) : branch M = true ↔ SparseCase M := by
  unfold branch
  rw [BranchTest.test_entries]
  simp only [SparseCase,entries,ne_eq,fieldSignature_eq_zero]

def branchComputes (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) :
    Computes (framedListEncoding (presentation M halg).encoding) encodingBoolBool
      (BranchTest.test (K:=field M)) :=
  BranchTest.computes (presentation M halg)

/-- The actual test run on the coefficient words internally produced from M.
This carries its real steps and timed output, rather than a Boolean promise. -/
def branch_outputs (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) :
    TM2OutputsInTime (branchComputes M halg).machine.computer
      ((framedListEncoding (presentation M halg).encoding).encode
        (BranchTest.entriesList (fieldSignature M)))
      (some (encodingBoolBool.encode (branch M)))
      ((branchComputes M halg).time.eval
        ((framedListEncoding (presentation M halg).encoding).encode
          (BranchTest.entriesList (fieldSignature M))).length) :=
  (branchComputes M halg).outputs (BranchTest.entriesList (fieldSignature M))

def fixedTemplates : ℕ → Template := Adjoin.templates 1 (fun _ => 4) chainTemplate
def templates_wellFormed : ∀ i < 2, (fixedTemplates i).WellFormed 1 1 (fun _ => 4) :=
  Adjoin.wellFormed chainTemplate chainTemplate_wellFormed
def compilerProof : ∀ i < 2,
    (fixedTemplates i).WellFormed 1 1 (fun _ => 4) ∧
      (fixedTemplates i).boundary = sourceArity fixedTemplates i :=
  compilerHypotheses fixedTemplates templates_wellFormed

abbrev SourceInput := ExactSignatureTables.Input 2 1 (sourceArity fixedTemplates)
abbrev TargetInput := ExactSignatureTables.Input 1 1 (fun _ => 4)
abbrev sourceEncoding := RawClosedNetwork.validatedEncoding 2 1 (sourceArity fixedTemplates)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding 1 1 (fun _ => 4)

/-- The fixed original family itself supplies the eight test words. On every
actual graph input, the finite constant-word writer emits those same canonical
field words and then runs the real parser/comparator. No branch or coefficient
list is accepted as an extra graph-input certificate. -/
def originalBranchComputes (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) :
    Computes sourceEncoding encodingBoolBool (fun _ : SourceInput => branch M) :=
  (constantComputes sourceEncoding (framedListEncoding (presentation M halg).encoding)
    (BranchTest.entriesList (fieldSignature M))).andThen (branchComputes M halg)

theorem originalBranch_primitive_bound (M : Signature L 4)
    (halg : ∀ t, IsAlgebraic ℚ (M t)) (r : SourceInput) :
    primitiveCost (originalBranchComputes M halg).machine
      ((originalBranchComputes M halg).outputs r).steps
      (some (initList (originalBranchComputes M halg).machine.computer
        (sourceEncoding.encode r))) ≤
      (primitivePolynomial (originalBranchComputes M halg)).eval
        (sourceEncoding.encode r).length :=
  computes_primitive_cost (originalBranchComputes M halg) r

/-- This is the existing complete finite Boolean-stack replacement program:
old M rows use the identity template; each new macro row emits two original M
rows and two X edges, with the computed fresh-edge offsets and ordered ports. -/
def query (r : SourceInput) : TargetInput :=
  Compiler.value 2 1 (sourceArity fixedTemplates) fixedTemplates 1 (fun _ => 4) compilerProof r

def queryComputes : Computes sourceEncoding targetEncoding query :=
  Compiler.computes 2 1 (sourceArity fixedTemplates) fixedTemplates 1 (fun _ => 4) compilerProof

theorem query_raw (r : SourceInput) : (query r).val = replace fixedTemplates r.val := rfl

theorem query_length_bound (r : SourceInput) :
    (targetEncoding.encode (query r)).length ≤
      queryComputes.outputBound.bound.eval (sourceEncoding.encode r).length :=
  queryComputes.outputBound.length_le r

theorem query_primitive_bound (r : SourceInput) :
    primitiveCost queryComputes.machine (queryComputes.outputs r).steps
      (some (initList queryComputes.machine.computer (sourceEncoding.encode r))) ≤
      (primitivePolynomial queryComputes).eval (sourceEncoding.encode r).length :=
  computes_primitive_cost queryComputes r

def targetValue (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) : TargetInput → field M :=
  (tables M halg).evaluate (presentation M halg)

def sourceValue (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) : SourceInput → field M :=
  (sourceTables fixedTemplates (tables M halg)
    (Adjoin.coordinates (presentation M halg) (tables M halg)
      chainTemplate chainTemplate_wellFormed)).evaluate (presentation M halg)

/-- Exact value identity for the literal query. Local macro coordinates are
produced by the existing template sum, not assumed as gate equations. -/
theorem query_value (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t))
    (r : SourceInput) : targetValue M halg (query r) = sourceValue M halg r := by
  let F := presentation M halg
  let T := tables M halg
  let source := fun i t => F.decode
    (Adjoin.coordinates F T chainTemplate chainTemplate_wellFormed i t)
  have hp := replacement_partition fixedTemplates r.val r.property templates_wellFormed
    source (fun i t => F.decode (T.vertex i t))
    (fun i a b => F.decode (T.edge i a b)) (fun _ => (1 : field M))
    (fun i => by
      simp only [one_smul]
      funext t
      exact (decode_templateCoordinates F fixedTemplates templates_wellFormed T i t).symm)
  change targetValue M halg (query r) =
    (∏ _v : Fin r.val.vertices.length, (1 : field M)) * sourceValue M halg r at hp
  simpa only [Finset.prod_const_one,one_mul] using hp

theorem target_value_exact (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t))
    (r : TargetInput) :
    ((targetValue M halg r : field M) : L) =
      (r.val.realize r.property (fun _ => M) (fun _ => Signature.disequality)).denote Fin.elim0 :=
  OriginalFamily.target_value_exact (coefficient M) (coefficient_algebraic M halg) r

theorem source_value_exact (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t))
    (r : SourceInput) :
    ((sourceValue M halg r : field M) : L) =
      (r.val.realize r.property
        (OriginalFamily.ambientSource (coefficient M) chainTemplate chainTemplate_wellFormed)
        (fun _ => Signature.disequality)).denote Fin.elim0 :=
  OriginalFamily.source_value_exact (coefficient M) (coefficient_algebraic M halg)
    chainTemplate chainTemplate_wellFormed r

/-- The adjoined source family contains exactly M and this actual macro.
Coincident signatures are not treated as distinct mathematical resources. -/
theorem source_family (M : Signature L 4) :
    Set.range (fun i : Fin 2 =>
      (⟨sourceArity fixedTemplates i.val,
        OriginalFamily.ambientSource (coefficient M) chainTemplate chainTemplate_wellFormed i⟩ :
          AnySignature L)) =
      {⟨4,M⟩} ∪ {⟨4,(nativeChain M).denote⟩} := by
  have h := OriginalFamily.ambientSource_family (coefficient M)
    chainTemplate chainTemplate_wellFormed
  rw [ambient_macro M] at h
  change Set.range (fun i : Fin 2 =>
      (⟨sourceArity fixedTemplates i.val,
        OriginalFamily.ambientSource (coefficient M) chainTemplate chainTemplate_wellFormed i⟩ :
          AnySignature L)) =
    Set.range (fun _ : Fin 1 => (⟨4,M⟩ : AnySignature L)) ∪
      {⟨4,(nativeChain M).denote⟩} at h
  have hold : Set.range (fun _ : Fin 1 => (⟨4,M⟩ : AnySignature L)) = {⟨4,M⟩} := by
    ext f
    constructor
    · rintro ⟨i,rfl⟩
      exact Set.mem_singleton _
    · intro hf
      have he : f = (⟨4,M⟩ : AnySignature L) := hf
      exact ⟨0,he.symm⟩
  rw [hold] at h
  exact h

abbrev Reduction (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) :=
  PolyTimeOracleReduction sourceEncoding (presentation M halg).encoding
    targetEncoding (presentation M halg).encoding (sourceValue M halg) (targetValue M halg)

/-- A controlled encoded one-query reduction from the ORIGINAL M plus its
actual two-copy macro to the SAME original M/native-X field oracle. It accepts
no hardness, reduction, normalization or local correctness premise. -/
def reduction (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) : Reduction M halg :=
  OriginalFamily.reduction (coefficient M) (coefficient_algebraic M halg)
    chainTemplate chainTemplate_wellFormed

theorem target_answer_length (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t))
    (r : TargetInput) :
    ((presentation M halg).encoding.encode (targetValue M halg r)).length ≤
      ((tables M halg).outputPolynomial (presentation M halg)).eval
        (targetEncoding.encode r).length :=
  (tables M halg).output_length_le (presentation M halg) r

attribute [local instance] Classical.propDecidable

/-- Only genuine mathematical consequences of the coefficient test are stored.
There is deliberately no Hard field or assumed six-vertex reduction. -/
structure SparseReceipt (M : Signature L 4) : Prop where
  sparse : SparseCase M
  actual_tensor : (nativeChain M).denote = table (sparseEntries (entries M))
  layer : Signature.SingleLayer (nativeChain M).denote 2
  mandatory :
    (nativeChain M).denote ![false,false,true,true] ≠ 0 ∧
    (nativeChain M).denote ![false,true,false,true] ≠ 0 ∧
    (nativeChain M).denote ![true,false,false,true] ≠ 0 ∧
    (nativeChain M).denote ![true,false,true,false] ≠ 0 ∧
    (nativeChain M).denote ![true,true,false,false] ≠ 0
  optional : (nativeChain M).denote ![false,true,true,false] =
    (entries M).c * (entries M).z + (entries M).d ^ 2
  support_card : (supportWords (nativeChain M).denote).card =
    if (entries M).c * (entries M).z + (entries M).d ^ 2 = 0 then 5 else 6

theorem sparseReceipt (M : Signature L 4) (hM : EvenSupport M)
    (hc : NonzeroCorners M) (hs : SparseCase M) : SparseReceipt M := by
  have hv := nativeChain_sparse M hM hs
  refine ⟨hs,hv,?_,?_,?_,?_⟩
  · rw [hv]
    exact sparse_singleLayer (entries M)
  · rw [hv]
    exact sparse_mandatory_entries M hc hs
  · rw [hv]
    exact sparse_optional_entry M
  · rw [hv]
    exact sparse_support_card M hc hs

/-- This is proof refinement of the actual Boolean branch result. Failed tests
retain none and are not interpreted as the external theorem's hard alternative. -/
def dispatch (M : Signature L 4) (hM : EvenSupport M) (hc : NonzeroCorners M) :
    Option (PLift (SparseReceipt M)) :=
  if ht : branch M = true then
    some ⟨sparseReceipt M hM hc ((branch_correct M).mp ht)⟩
  else none

theorem dispatch_none (M : Signature L 4) (hM : EvenSupport M) (hc : NonzeroCorners M) :
    dispatch M hM hc = none ↔ ¬SparseCase M := by
  by_cases hs : SparseCase M
  · have ht := (branch_correct M).mpr hs
    simp [dispatch,ht,hs]
  · have ht : branch M ≠ true := fun h => hs ((branch_correct M).mp h)
    simp [dispatch,ht,hs]

/-- Exact original external theorem hypotheses over algebraic complex numbers.
The shared U condition is checked for the edge and M together. This packet
does not assert that an unsuccessful common-basis search implies hardness. -/
structure OriginalConditions (M : Signature Holant.Tractable.AlgebraicComplex 4) : Prop where
  support : EvenSupport M
  corners : NonzeroCorners M
  no_affine : ¬Holant.Tractable.CommonKPresentationInKCoordinates
    Holant.Tractable.affineClass {⟨4,M⟩}
  no_product : ¬Holant.Tractable.CommonKPresentationInKCoordinates
    Holant.Tractable.productClass {⟨4,M⟩}
  no_localAffine : ¬Holant.Tractable.CommonKPresentationInKCoordinates
    Holant.Tractable.localAffineClass {⟨4,M⟩}

/-- Consumer of the complete original nonexception packet. Every case not
handled by the sparse construction is retained in the none branch. -/
def original_dispatch (M : Signature Holant.Tractable.AlgebraicComplex 4)
    (h : OriginalConditions M) : Option (PLift (SparseReceipt M)) :=
  dispatch M h.support h.corners

theorem original_dispatch_none (M : Signature Holant.Tractable.AlgebraicComplex 4)
    (h : OriginalConditions M) : original_dispatch M h = none ↔ ¬SparseCase M :=
  dispatch_none M h.support h.corners

theorem original_sparse_exclusions (M : Signature Holant.Tractable.AlgebraicComplex 4)
    (h : OriginalConditions M) (ht : branch M = true) :
    ¬Holant.Tractable.Affine (nativeChain M).denote ∧
      ¬Holant.Tractable.Product (nativeChain M).denote :=
  nativeChain_exclusions M h.support h.corners ((branch_correct M).mp ht)

end Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
