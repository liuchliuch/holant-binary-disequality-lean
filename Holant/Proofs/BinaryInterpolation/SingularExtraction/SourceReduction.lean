import Holant.Proofs.BinaryInterpolation.SingularExtraction.CommonField
import Holant.Proofs.BinaryInterpolation.SingularExtraction.SourceSemantics


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.SourceReduction
open Holant Holant.Tractable Holant.Complexity
open Holant.Complexity.UniversalPairReduction.ThreeQuery
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (hs : ¬ CommonOneSided (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex))))
variable (u v : Bool → AlgebraicComplex) (hu : u ≠ 0) (hv : v ≠ 0)
variable (hB : Gadget.Realizes (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex)))
  .disequality (outerSignature u v))

/-- These are fixed existence choices made before graph input. Their local
realization proofs were constructed by majority contraction and physical caps. -/
def macros : PowerMacro G u × PowerMacro G v :=
  Classical.choice (source_labelled_powers G hs u v hu hv hB)
abbrev leftMacro := (macros G hs u v hu hv hB).1
abbrev rightMacro := (macros G hs u v hu hv hB).2

abbrev field := CommonField.field G u v (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB)
abbrev presentation := CommonField.presentation G u v
  (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB)
abbrev sourceValue := CommonField.sourceValue G u v
  (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB)
abbrev targetValue := CommonField.targetValue G u v
  (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB)
abbrev inputEncoding := FieldReduction.inputEncoding (s:=s) (arity:=arity)
abbrev queryEncoding := FieldReduction.queryEncoding (s:=s) (arity:=arity)
abbrev outputEncoding := (presentation G hs u v hu hv hB).encoding

def reduction : PolyTimeOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (outputEncoding G hs u v hu hv hB)
    (queryEncoding (s:=s) (arity:=arity)) (outputEncoding G hs u v hu hv hB)
    (sourceValue G hs u v hu hv hB) (targetValue G hs u v hu hv hB) :=
  CommonField.reduction G u v (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB)

theorem source_exact (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    (sourceValue G hs u v hu hv hB r : AlgebraicComplex) =
      (r.val.realize r.property
        (Tables.typed (Tables.familyTable G u v) (s+2) (Tables.adjoinedArity s arity 1 1))
        (fun _ => Signature.disequality)).denote Fin.elim0 :=
  CommonField.source_exact G u v _ _ r

theorem target_exact (r : ExactSignatureTables.Input s 1 arity) :
    (targetValue G hs u v hu hv hB r : AlgebraicComplex) =
      (r.val.realize r.property G (fun _ => Signature.disequality)).denote Fin.elim0 :=
  CommonField.target_exact G u v _ _ r

/-- The presentation is faithful even after returning to literal complex
numbers; equal rational-coordinate answers cannot identify unequal values. -/
def complexEmbedding : field G hs u v hu hv hB →+* ℂ :=
  (algebraicClosure ℚ ℂ).subtype.comp
    (CommonField.field G u v (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB)).subtype

theorem complexEmbedding_injective : Function.Injective (complexEmbedding G hs u v hu hv hB) :=
  (complexEmbedding G hs u v hu hv hB).injective

abbrev timePolynomial := CommonField.timePolynomial G u v
  (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB)
abbrev primitivePolynomial := CommonField.primitivePolynomial G u v
  (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB)
abbrev budget := CommonField.budget G u v
  (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB)

/-- End-to-end execution from the original bytes, exact one original-Γ call,
and a primitive bound in those same bytes. No oracle-dependent polynomial and
no promise of equal occurrence counts is introduced. -/
theorem run_cost (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (queryEncoding (s:=s) (arity:=arity)) (outputEncoding G hs u v hu hv hB)
      (targetValue G hs u v hu hv hB) oracle)
    (r : OriginalQuery.UnaryInput (s:=s) (arity:=arity)) :
    ∃ t ≤ (timePolynomial G hs u v hu hv hB).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length,
      (fun p => p.bind ((reduction G hs u v hu hv hB).machine.step oracle))^[t]
        (some ((reduction G hs u v hu hv hB).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r))) =
        some ((reduction G hs u v hu hv hB).machine.output
          ((outputEncoding G hs u v hu hv hB).encode (sourceValue G hs u v hu hv hB r))) ∧
      queryCount (reduction G hs u v hu hv hB).machine oracle
        ((reduction G hs u v hu hv hB).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t = 1 ∧
      OracleBatch.primitiveCount (reduction G hs u v hu hv hB).machine oracle
        ((reduction G hs u v hu hv hB).machine.init ((inputEncoding (s:=s) (arity:=arity)).encode r)) t ≤
        (primitivePolynomial G hs u v hu hv hB).eval ((inputEncoding (s:=s) (arity:=arity)).encode r).length :=
  FieldReduction.run_cost (presentation G hs u v hu hv hB)
    (CommonField.original G u v (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB))
    (CommonField.left G u v (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB))
    (CommonField.right G u v (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB))
    (CommonField.leftMacro G u v (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB))
    (CommonField.rightMacro G u v (leftMacro G hs u v hu hv hB) (rightMacro G hs u v hu hv hB)) oracle ho r

/-- Source hypotheses alone now produce an actual machine term. Retention can
be added by callers without changing this stronger local statement. -/
theorem has_reduction : Nonempty (PolyTimeOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (outputEncoding G hs u v hu hv hB)
    (queryEncoding (s:=s) (arity:=arity)) (outputEncoding G hs u v hu hv hB)
    (sourceValue G hs u v hu hv hB) (targetValue G hs u v hu hv hB)) :=
  ⟨reduction G hs u v hu hv hB⟩

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.SourceReduction
