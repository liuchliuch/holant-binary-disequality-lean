import Holant.Complexity.EdgeSubdivision.WireMacros
import Holant.Complexity.EdgeSubdivision.Reduction

/-! Swap the literal extra binary and structural wire by two exact graph
substitutions. Scalar cycles are retained as graphs, so no cycle factor is lost. -/
namespace Holant.Complexity.EdgeSubdivision.WireEquivalence
open Computability BinaryCompose Holant.Algebraic FixedGadgetSubstitution
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

variable (s : ℕ) (arity : ℕ → ℕ)
abbrev Input := ExactSignatureTables.Input (s+1) 1 (targetArity s arity)

def query (r : Input s arity) : Input s arity :=
  VertexSubstitution.value (WireMacros.templates s arity) (WireMacros.boundary s arity)
    (WireMacros.valid s arity) (Compiler.value (s+1) 1 (targetArity s arity) r)

def computes : Computes (RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s arity))
    (RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s arity)) (query s arity) :=
  (Compiler.computes (s+1) 1 (targetArity s arity)).andThen
    (VertexSubstitution.computes (WireMacros.templates s arity) (WireMacros.boundary s arity)
      (WireMacros.valid s arity))

section Semantic
variable {s arity} {K : Type} [CommSemiring K]
variable (source : (i : Fin s) → Signature K (arity i.val))

def value (p q : Bool) (r : Input s arity) : K :=
  (r.val.realize r.property
    (extendedSignatures source (fun _ : Fin 1 => WirePath.kernel p))
    (fun _ : Fin 1 => WirePath.kernel q)).denote Fin.elim0

theorem query_value (p q : Bool) (r : Input s arity) :
    value source q p (query s arity r) = value source p q r := by
  have hsub := subdivision_partition_value r.val r.property
    (extendedSignatures source (fun _ : Fin 1 => WirePath.kernel p))
    (fun _ : Fin 1 => WirePath.kernel q) (fun _ : Fin 1 => WirePath.kernel q)
    (WirePath.kernel p) (fun _ a c => WirePath.kernel_sandwich p q a c)
  have hmacro := VertexSubstitution.partition (WireMacros.templates s arity)
    (WireMacros.boundary s arity) (WireMacros.valid s arity)
    (subdivide (s+1) r.val) (queryValid (s+1) r.val r.property)
    (WireMacros.middleSignatures source p q)
    (extendedSignatures source (fun _ : Fin 1 => WirePath.kernel q))
    (fun _ : Fin 1 => WirePath.kernel p)
    (fun i => funext (WireMacros.macro_value source p q i))
  exact hmacro.trans hsub

end Semantic
variable {s arity} {K : Type} {n : ℕ} [Field K] [Algebra ℚ K]
variable (F : FixedField K n)
variable (coordinates : (i : Fin s) → Signature (Fin n → ℚ) (arity i.val))

def kernelCoordinates (p : Bool) (a c : Bool) : Fin n → ℚ :=
  F.decode.symm (WirePath.kernel p a c)

def tables (p q : Bool) : ExactSignatureTables n (s+1) 1 (targetArity s arity) where
  vertex := extendedSignatures coordinates (fun _ : Fin 1 => kernelCoordinates F p)
  edge _ := kernelCoordinates F q

theorem decoded_signatures (p : Bool) :
    (fun i x => F.decode (extendedSignatures coordinates
      (fun _ : Fin 1 => kernelCoordinates F p) i x)) =
      extendedSignatures (fun i x => F.decode (coordinates i x))
        (fun _ : Fin 1 => WirePath.kernel p) := by
  funext i x
  unfold extendedSignatures
  split <;> simp [kernelCoordinates]

theorem evaluate_eq (p q : Bool) (r : Input s arity) :
    (tables F coordinates p q).evaluate F r =
      value (fun i x => F.decode (coordinates i x)) p q r := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change (r.val.realize r.property
    (fun i x => F.decode (extendedSignatures coordinates (fun _ : Fin 1 => kernelCoordinates F p) i x))
    (fun _ a c => F.decode (kernelCoordinates F q a c))).denote Fin.elim0 = _
  rw [decoded_signatures]
  simp only [kernelCoordinates,LinearEquiv.apply_symm_apply]
  rfl

/-- Every call and answer bit is charged by the actual one-query program. The
same fixed coefficient field and answer codec are used in both directions. -/
def reduction (p q : Bool) : PolyTimeOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s arity)) F.encoding
    (RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s arity)) F.encoding
    ((tables F coordinates p q).evaluate F) ((tables F coordinates q p).evaluate F) :=
  OracleOneQuery.of_eq (computes s arity) (identityComputes F.encoding)
    ((tables F coordinates q p).outputBound F) ((tables F coordinates p q).evaluate F)
    (fun r => by
      rw [evaluate_eq,evaluate_eq]
      exact (query_value (fun i x => F.decode (coordinates i x)) p q r).symm)

end
end Holant.Complexity.EdgeSubdivision.WireEquivalence
