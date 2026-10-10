import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.SelfLoop
import Holant.Proofs.Reductions.EightVertexNonexception.Source
import Holant.Proofs.BinaryInterpolation.OriginalTables
import Holant.Proofs.BinaryInterpolation.MachineCapstone


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation
open Holant.Complexity.BinaryInterpolation.Chains
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace Original
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (coefficient coefficient_algebraic field presentation tables fixedTemplates
   templates_wellFormed query queryComputes query_value targetValue sourceValue
   TargetInput SourceInput targetEncoding sourceEncoding ambient_macro branch
   branch_correct branchComputes fieldSignature)
end Original
namespace PQ
export Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries
  (A Source Sample newLabel recovery)
end PQ
namespace OT
export Holant.LocalDrafts.BinaryInterpolation.OriginalTables
  (tables tables_new tables_local binarySlot binarySlot_new right_eq_binarySlot)
end OT
namespace MC
export Holant.LocalDrafts.BinaryInterpolation.MachineCapstone
  (Data Input values denominator resultPair interpolatedValue answer_order
   codeEncoding post postTime post_outputs answered transcriptBound
   interpreter arithmetic arithmetic_outputs widthPolynomial result_length)
end MC

abbrev baseArity := sourceArity Original.fixedTemplates

/-- Literal port order [edge false, edge true, boundary 0, boundary 1].
The vertex label is the original q slot, namely 1, not a free binary table. -/
def loopLabelling {K : Type*} [CommSemiring K] (q : Signature K 4) :
    Labelling (selfLoop q).shape 2 1 baseArity where
  vertex := fun _ => 1
  vertex_arity := fun _ => rfl
  edge := fun _ => 0

def loopTemplate : Template := (loopLabelling (0 : Signature ℕ 4)).template

theorem loopTemplate_wellFormed : loopTemplate.WellFormed 2 1 baseArity :=
  (loopLabelling (0 : Signature ℕ 4)).wellFormed
theorem loopTemplate_boundary : loopTemplate.boundary = 2 := rfl
theorem loopTemplate_records :
    loopTemplate.vertices = [(1,[.inr (0,false),.inr (0,true),.inl 0,.inl 1])] ∧
      loopTemplate.edges = [0] := by
  constructor <;> rfl

variable {L : Type} [Field L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t))

/-- Use the ORIGINAL intermediate-field algebra inherited from the given
ambient rational algebra, exactly as familyPresentation does. This is a local
instance selection, not a new field/presentation or an algebraicity premise. -/
local instance originalFieldAlgebra : Algebra ℚ (Original.field M) :=
  (Original.field M).algebra'

abbrev F (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) :=
  Original.presentation M halg
def baseTables (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) :=
  sourceTables Original.fixedTemplates (Original.tables M halg)
  (Adjoin.coordinates (F M halg) (Original.tables M halg)
    chainTemplate chainTemplate_wellFormed)

def baseSignatures (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t))
    (i : Fin 2) : Signature (Original.field M) (baseArity i.val) :=
  fun t => (F M halg).decode ((baseTables M halg).vertex i t)
def kernels (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t))
    (i : Fin 1) (a b : Bool) : Original.field M :=
  (F M halg).decode ((baseTables M halg).edge i a b)

theorem kernels_exact : kernels M halg = fun _ => Signature.disequality := by
  funext i a b
  apply Subtype.ext
  have h := familyCoordinates_spec (Original.coefficient M)
    (Original.coefficient_algebraic M halg) (.inr (i,a,b))
  cases a <;> cases b <;> exact h

theorem base_signatures_exact (i : Fin 2) (t : Fin (baseArity i.val) → Bool) :
    ((baseSignatures M halg i t : Original.field M) : L) =
      OriginalFamily.ambientSource (Original.coefficient M)
        chainTemplate chainTemplate_wellFormed i t := by
  change (((F M halg).decode (templateCoordinates (F M halg) Original.fixedTemplates
    Original.templates_wellFormed (Original.tables M halg) i t) : Original.field M) : L) = _
  rw [decode_templateCoordinates]
  exact OriginalFamily.macro_value_exact (Original.coefficient M)
    (Original.coefficient_algebraic M halg) (Original.fixedTemplates i.val)
      (Original.templates_wellFormed i.val i.isLt) t

/-- The actual q slot, coefficient by coefficient, embeds back into the
original ambient L. This uses the saved template's sum and original codec. -/
theorem q_exact (t : Word) :
    ((baseSignatures M halg (1 : Fin 2) t : Original.field M) : L) =
      (nativeChain M).denote t := by
  change (( (F M halg).decode
    (templateCoordinates (F M halg) Original.fixedTemplates
      Original.templates_wellFormed (Original.tables M halg) (1 : Fin 2) t)
      : Original.field M) : L) = _
  rw [decode_templateCoordinates]
  change (((chainTemplate.network chainTemplate_wellFormed
    (fun i t => (F M halg).decode ((Original.tables M halg).vertex i t))
    (fun i a b => (F M halg).decode ((Original.tables M halg).edge i a b))).denote t
      : Original.field M) : L) = _
  exact (OriginalFamily.macro_value_exact (Original.coefficient M)
    (Original.coefficient_algebraic M halg) chainTemplate chainTemplate_wellFormed t).trans
      (congrFun (Original.ambient_macro M) t)

def u (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) : Original.field M :=
  baseSignatures M halg 1 ![false,true,false,true] +
    baseSignatures M halg 1 ![true,false,false,true]
def v (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) : Original.field M :=
  baseSignatures M halg 1 ![false,true,true,false] +
    baseSignatures M halg 1 ![true,false,true,false]

theorem u_exact (hM : EvenSupport M) (hs : SparseCase M) :
    ((u M halg : Original.field M) : L) = sparseU (entries M) := by
  change ((baseSignatures M halg 1 ![false,true,false,true] : Original.field M) : L) +
    ((baseSignatures M halg 1 ![true,false,false,true] : Original.field M) : L) = _
  rw [q_exact,q_exact,nativeChain_sparse M hM hs]
  simp [table,sparseEntries,sparseU] <;> ring

theorem v_exact (hM : EvenSupport M) (hs : SparseCase M) :
    ((v M halg : Original.field M) : L) = sparseV (entries M) := by
  change ((baseSignatures M halg 1 ![false,true,true,false] : Original.field M) : L) +
    ((baseSignatures M halg 1 ![true,false,true,false] : Original.field M) : L) = _
  rw [q_exact,q_exact,nativeChain_sparse M hM hs] <;> rfl

theorem loopTemplate_denote :
    (loopTemplate.network loopTemplate_wellFormed
      (baseSignatures M halg) (kernels M halg)).denote =
      (selfLoop (baseSignatures M halg (1 : Fin 2))).denote := by
  let q := baseSignatures M halg (1 : Fin 2)
  change ((loopLabelling q).template.network (loopLabelling q).wellFormed
    (baseSignatures M halg) (kernels M halg)).denote = (selfLoop q).denote
  apply Labelling.denote_template_of_labels (loopLabelling q)
    (baseSignatures M halg) (kernels M halg) (selfLoop q).vertex (selfLoop q).edge
  · intro i t
    rfl
  · intro e a b
    rw [kernels_exact]
    exact congrFun₂ (selfLoop_edge q e).symm a b

theorem loop_binary (hM : EvenSupport M) (hs : SparseCase M) :
    (loopTemplate.network loopTemplate_wellFormed
      (baseSignatures M halg) (kernels M halg)).denote =
      binarySignature (weightedX (u M halg) (v M halg)) := by
  rw [loopTemplate_denote]
  funext t
  rw [selfLoop_sum]
  change _ = weightedX (u M halg) (v M halg) (t 0) (t 1)
  cases h₀ : t 0 <;> cases h₁ : t 1
  · change baseSignatures M halg 1 ![false,true,false,false] +
      baseSignatures M halg 1 ![true,false,false,false] = 0
    apply Subtype.ext
    change ((baseSignatures M halg 1 ![false,true,false,false] : Original.field M) : L) +
      ((baseSignatures M halg 1 ![true,false,false,false] : Original.field M) : L) = 0
    rw [q_exact,q_exact,nativeChain_sparse M hM hs]
    simp [table,sparseEntries]
  · change baseSignatures M halg 1 ![false,true,false,true] +
      baseSignatures M halg 1 ![true,false,false,true] = u M halg
    rfl
  · change baseSignatures M halg 1 ![false,true,true,false] +
      baseSignatures M halg 1 ![true,false,true,false] = v M halg
    rfl
  · change baseSignatures M halg 1 ![false,true,true,true] +
      baseSignatures M halg 1 ![true,false,true,true] = 0
    apply Subtype.ext
    change ((baseSignatures M halg 1 ![false,true,true,true] : Original.field M) : L) +
      ((baseSignatures M halg 1 ![true,false,true,true] : Original.field M) : L) = 0
    rw [q_exact,q_exact,nativeChain_sparse M hM hs]
    simp [table,sparseEntries]

/-- This record contains only actual fixed data. In particular it has no
nodes-injective, desired reduction, gate-correctness or hardness field. -/
def data (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) :
    MC.Data (F M halg) (baseTables M halg) where
  template := loopTemplate
  valid := loopTemplate_wellFormed
  binary := loopTemplate_boundary
  edge := 0
  gamma := v M halg
  rho := u M halg / v M halg
  geometric := true

abbrev Input (M : Signature L 4) (halg : ∀ t, IsAlgebraic ℚ (M t)) := MC.Input (data M halg)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding 3 1
  (PQ.A (s:=2) baseArity loopTemplate)
abbrev Sample := PQ.Sample (s:=2) (b:=1) baseArity loopTemplate

/-- One finite query program for the input-dependent positive exponent k+1.
It first emits q self-loops and chain connectors, then expands each q back
into its actual two original M occurrences and two original native-X edges. -/
def sampleQuery (x : Sample) : Original.TargetInput :=
  Original.query (Compiler.OriginalFamily.value baseArity loopTemplate
    loopTemplate_wellFormed loopTemplate_boundary (0 : Fin 1) x)

def sampleQueryComputes : Computes
    (Compiler.OriginalFamily.inputEncoding (s:=2) (b:=1) baseArity loopTemplate)
    Original.targetEncoding sampleQuery :=
  (Compiler.OriginalFamily.computes baseArity loopTemplate
    loopTemplate_wellFormed loopTemplate_boundary (0 : Fin 1)).andThen Original.queryComputes

theorem sampleQuery_value (x : Sample) :
    Original.targetValue M halg (sampleQuery x) =
      (baseTables M halg).evaluate (F M halg)
        (Compiler.OriginalFamily.value baseArity loopTemplate
          loopTemplate_wellFormed loopTemplate_boundary (0 : Fin 1) x) :=
  Original.query_value M halg _

def targetPinValue (r : Input M halg) : Original.field M :=
  (r.val.realize r.property
    (OT.binarySlot loopTemplate loopTemplate_wellFormed (baseSignatures M halg)
      (kernels M halg) loopTemplate_boundary rightPin) (kernels M halg)).denote Fin.elim0

/-- Ordered entrywise embedding into the same original ambient L; the old
slots have base_signatures_exact and the new slot is the literal 01 pin. -/
def ambientPinValue (r : Input M halg) : L :=
  (r.val.realize r.property
    (fun i t => ((OT.binarySlot loopTemplate loopTemplate_wellFormed
      (baseSignatures M halg) (kernels M halg) loopTemplate_boundary rightPin i t
        : Original.field M) : L))
    (fun i a b => ((kernels M halg i a b : Original.field M) : L))).denote Fin.elim0

theorem target_pin_value_exact (r : Input M halg) :
    ((targetPinValue M halg r : Original.field M) : L) = ambientPinValue M halg r := by
  unfold targetPinValue ambientPinValue
  change (Original.field M).subtype _ = _
  rw [← Network.denote_map (Original.field M).subtype] <;> rfl

theorem values_denote (r : Input M halg) (i : Fin (occurrences 2 r.val+1)) :
    MC.values (data M halg) r i =
      ((Compiler.OriginalFamily.value baseArity loopTemplate loopTemplate_wellFormed
        loopTemplate_boundary (0 : Fin 1) ⟨r,i⟩).val.realize
        (Compiler.OriginalFamily.value baseArity loopTemplate loopTemplate_wellFormed
          loopTemplate_boundary (0 : Fin 1) ⟨r,i⟩).property
        (baseSignatures M halg) (kernels M halg)).denote Fin.elim0 := by
  rw [MC.values,ExactSignatureTables.evaluate_eq_decoded] <;> rfl

/-- General finite interpolation receipt: its only node condition is the
nonzero *actual denominator produced by the same program*. No infinite-order
or all-input separation conclusion is assumed. -/
theorem recovery_if_denominator (hM : EvenSupport M) (hs : SparseCase M)
    (r : Input M halg) (hv : v M halg ≠ 0)
    (hd : (MC.resultPair (data M halg) r).2 ≠ 0) :
    MC.interpolatedValue (data M halg) r = targetPinValue M halg r := by
  let G : (i : Fin 2) → Signature (Original.field M) (baseArity i.val) := baseSignatures M halg
  let E : Fin 1 → Bool → Bool → Original.field M := kernels M halg
  let S := OT.tables loopTemplate loopTemplate_wellFormed G E
  let L₀ := OT.binarySlot loopTemplate loopTemplate_wellFormed G E loopTemplate_boundary leftPin
  let R₀ := OT.binarySlot loopTemplate loopTemplate_wellFormed G E loopTemplate_boundary rightPin
  let B := weightedX (u M halg) (v M halg)
  let nodes := WeightFormulas.nodes true (u M halg / v M halg) (occurrences 2 r.val)
  have hden : commonDenominator (queryDenominator nodes
      (WeightFormulas.scales (v M halg) (occurrences 2 r.val))) ≠ 0 := by
    change commonDenominator (queryDenominator nodes
      (WeightFormulas.scales (v M halg) (occurrences 2 r.val))) ≠ 0 at hd
    exact hd
  have hn : Function.Injective nodes := nodes_injective_of_denominator nodes
    (WeightFormulas.scales (v M halg) (occurrences 2 r.val)) hden
  have hB : (⟨PQ.A (s:=2) baseArity loopTemplate 2,S PQ.newLabel⟩ :
      AnySignature (Original.field M)) = ⟨2,binarySignature B⟩ :=
    (OT.tables_new loopTemplate loopTemplate_wellFormed G E).trans
      (congrArg (fun f : Signature (Original.field M) 2 =>
        (⟨2,f⟩ : AnySignature (Original.field M))) (loop_binary M halg hM hs))
  have hp := PQ.recovery baseArity loopTemplate loopTemplate_wellFormed
    loopTemplate_boundary (0 : Fin 1) S L₀ R₀ G E B leftPin rightPin
    (v M halg) (fun t => (u M halg/v M halg)^t) hB
    (OT.binarySlot_new loopTemplate loopTemplate_wellFormed G E loopTemplate_boundary leftPin)
    (OT.binarySlot_new loopTemplate loopTemplate_wellFormed G E loopTemplate_boundary rightPin)
    (congrFun (kernels_exact M halg) (0 : Fin 1))
    (power_pencil (u M halg) (v M halg) hv) 1
    (OT.tables_local loopTemplate loopTemplate_wellFormed G E) r one_ne_zero hv hn
  simp only [one_mul] at hp
  rw [OT.right_eq_binarySlot loopTemplate loopTemplate_wellFormed G E
    loopTemplate_boundary rightPin] at hp
  have hvalues : (fun i : Fin (occurrences 2 r.val+1) => MC.values (data M halg) r i) =
      (fun i => ((Compiler.OriginalFamily.value baseArity loopTemplate
        loopTemplate_wellFormed loopTemplate_boundary (0 : Fin 1) ⟨r,i⟩).val.realize
        (Compiler.OriginalFamily.value baseArity loopTemplate loopTemplate_wellFormed
          loopTemplate_boundary (0 : Fin 1) ⟨r,i⟩).property G E).denote Fin.elim0) := by
    funext i
    exact values_denote M halg r i
  have hc : ∀ i : Fin (occurrences 2 r.val+1),
      WeightFormulas.scales (v M halg) (occurrences 2 r.val) i ≠ 0 :=
    fun i => pow_ne_zero _ hv
  change commonNumerator (queryDenominator nodes
      (WeightFormulas.scales (v M halg) (occurrences 2 r.val))) (MC.values (data M halg) r) /
    commonDenominator (queryDenominator nodes
      (WeightFormulas.scales (v M halg) (occurrences 2 r.val))) = targetPinValue M halg r
  rw [← recover_normalized_common nodes
    (WeightFormulas.scales (v M halg) (occurrences 2 r.val)) (MC.values (data M halg) r) hn hc]
  simp_rw [congrFun hvalues]
  have hnodes : nodes = (fun i => (u M halg / v M halg)^(i.val+1)) := by
    funext i
    rfl
  rw [hnodes]
  simpa only [nodes,WeightFormulas.nodes,WeightFormulas.scales,if_true,pow_mul,
    data,OT.binarySlot,targetPinValue,G,E,R₀] using hp

/-- A repeated node is an explicitly retained failure. Field division is
total and the actual machine then outputs zero; this is not a pin or Hard. -/
theorem zero_denominator (r : Input M halg)
    (hd : (MC.resultPair (data M halg) r).2 = 0) :
    MC.interpolatedValue (data M halg) r = 0 := by
  simp only [MC.interpolatedValue,hd,div_zero]

end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
