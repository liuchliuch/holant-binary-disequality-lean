import Holant.Complexity.FixedFieldMachines.RawGraphEvaluator.Composition
import Holant.Algebraic.FiniteFamilyOneHot

/-! The coefficient field and rational coordinates are derived from the actual
fixed finite algebraic family. The output is decoded to the unchanged ambient
network sum, with no per-input field or free arithmetic oracle. -/
namespace Holant.Complexity.FixedFieldMachines.RawGraphEvaluator
open Turing Computability BinaryCompose Holant.Algebraic Holant.Algebraic.FixedField
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open Holant.Complexity.ExactSignatureTables
open Holant.Complexity.GraphPreprocessing.OriginalCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
noncomputable section
variable {L : Type} [Field L] [Algebra ℚ L] {s b : ℕ} {arity : ℕ→ℕ}

 def familyLabels (x : GraphListCompiler.Input s b arity) :
    FamilyNetwork (A:=CoefficientIndex s b arity) 0 where
  shape:=x.val.shape x.property
  vertexLabel v w:=.inl ⟨x.val.signatureLabel x.property v,w⟩
  edgeLabel e a b:=.inr (x.val.edgeLabel x.property e,a,b)

 def ambientNetwork (coeff : CoefficientIndex s b arity→L)
    (x : GraphListCompiler.Input s b arity) : Holant.Network L 0 :=
  x.val.realize x.property (fun i w=>coeff (.inl ⟨i,w⟩))
    (fun i a b=>coeff (.inr (i,a,b)))

 theorem common_network_eq (coeff : CoefficientIndex s b arity→L)
    (halg : ∀a,IsAlgebraic ℚ (coeff a)) (x : GraphListCompiler.Input s b arity) :
    network (familyPresentation coeff halg) (familyCoordinates coeff halg) x=
      commonFieldNetwork coeff halg (familyLabels x) := rfl

 theorem ambient_network_eq (coeff : CoefficientIndex s b arity→L)
    (x : GraphListCompiler.Input s b arity) :
    ambientNetwork coeff x=familyAmbientNetwork coeff (familyLabels x) := rfl

 theorem common_value_exact (coeff : CoefficientIndex s b arity→L)
    (halg : ∀a,IsAlgebraic ℚ (coeff a)) (x : GraphListCompiler.Input s b arity) :
    ((value (familyPresentation coeff halg) (familyCoordinates coeff halg) x : familyField coeff) : L)=
      (ambientNetwork coeff x).denote Fin.elim0 := by
  rw [value,common_network_eq,ambient_network_eq]
  exact commonFieldNetwork_denote coeff halg (familyLabels x) Fin.elim0

 theorem common_valid (coeff : CoefficientIndex s b arity→L)
    (halg : ∀a,IsAlgebraic ℚ (coeff a)) (x : GraphListCompiler.Input s b arity)
    (hf : ∀v,Signature.OneHot ((ambientNetwork coeff x).vertex v))
    (hX : ∀e,(ambientNetwork coeff x).edge e=Signature.disequality) :
    Valid (familyPresentation coeff halg) (familyCoordinates coeff halg) x := by
  unfold Valid
  rw [common_network_eq]
  exact ⟨commonFieldNetwork_oneHot coeff halg (familyLabels x) hf,
    commonFieldNetwork_disequality coeff halg (familyLabels x) hX⟩

 theorem finite_family_evaluate_of_compiler_correct (hc : CompilerCorrect s b arity)
    (coeff : CoefficientIndex s b arity→L) (halg : ∀a,IsAlgebraic ℚ (coeff a))
    (x : GraphListCompiler.Input s b arity)
    (hf : ∀v,Signature.OneHot ((ambientNetwork coeff x).vertex v))
    (hX : ∀e,(ambientNetwork coeff x).edge e=Signature.disequality) :
    let F:=familyPresentation coeff halg
    let cs:=familyCoordinates coeff halg
    ∃time,∃answer : familyField coeff,
      (answer:L)=(ambientNetwork coeff x).denote Fin.elim0 ∧
      time≤(timePolynomial F cs).eval (RawClosedNetwork.encoding.encode x.val).length ∧
      Kernels.Executes (machine F cs) (RawClosedNetwork.encoding.encode x.val)
        (F.encoding.encode answer) time ∧
      primitiveCost (machine F cs) time
        (some (initList (machine F cs).computer (RawClosedNetwork.encoding.encode x.val)))≤
        (primitivePolynomial F cs).eval (RawClosedNetwork.encoding.encode x.val).length := by
  obtain ⟨t,ht,hr,hp⟩:=execute_with_primitive_cost_of_compiler_correct hc
    (familyPresentation coeff halg) (familyCoordinates coeff halg) x
    (common_valid coeff halg x hf hX)
  exact ⟨t,_,common_value_exact coeff halg x,ht,hr,hp⟩

 theorem finite_family_arithmetic_bound (coeff : CoefficientIndex s b arity→L)
    (halg : ∀a,IsAlgebraic ℚ (coeff a)) (x : GraphListCompiler.Input s b arity)
    (hf : ∀v,Signature.OneHot ((ambientNetwork coeff x).vertex v))
    (hX : ∀e,(ambientNetwork coeff x).edge e=Signature.disequality) :
    (((network (familyPresentation coeff halg) (familyCoordinates coeff halg) x).computedOneHotProgram.run.1 : familyField coeff):L)=
      (ambientNetwork coeff x).denote Fin.elim0 ∧
    (network (familyPresentation coeff halg) (familyCoordinates coeff halg) x).computedOneHotProgram.run.2≤
      11*(x.val.vertices.length+x.val.edges.length) := by
  rw [common_network_eq,ambient_network_eq]
  exact finiteFamily_oneHot_program coeff halg (familyLabels x) hf hX

end
end Holant.Complexity.FixedFieldMachines.RawGraphEvaluator
