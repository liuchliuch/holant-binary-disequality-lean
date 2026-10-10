import Holant.Complexity.EdgeSubdivision.Compile
import Holant.Complexity.EdgeSubdivision.RawSemantics
import Holant.Complexity.EncodedHolantOutputSize
import Holant.Complexity.OracleOneQuery.Reduction

/-! A genuine one-query reduction implementing literal edge subdivision in one
fixed coefficient field, including the cost of copying the encoded answer. -/
namespace Holant.Complexity.EdgeSubdivision
open Computability BinaryCompose Holant.Algebraic
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n s b arity)
variable (binary : Fin b → Bool → Bool → (Fin n → ℚ))
variable (wire : Bool → Bool → (Fin n → ℚ))

def targetTables : ExactSignatureTables n (s+b) 1 (targetArity s arity) where
  vertex := extendedSignatures T.vertex binary
  edge _ := wire

theorem decode_extended (i : Fin (s+b))
    (x : Fin (targetArity s arity i.val) → Bool) :
    F.decode (extendedSignatures T.vertex binary i x) =
      extendedSignatures (fun j y => F.decode (T.vertex j y))
        (fun j a c => F.decode (binary j a c)) i x := by
  unfold extendedSignatures
  split <;> rfl

theorem evaluate_subdivision
    (hfuse : ∀ j a c, (∑ uv : Bool×Bool,
      F.decode (wire a uv.1) * F.decode (binary j uv.1 uv.2) * F.decode (wire uv.2 c)) =
        F.decode (T.edge j a c))
    (r : ExactSignatureTables.Input s b arity) :
    (targetTables T binary wire).evaluate F (Compiler.value s b arity r) = T.evaluate F r := by
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  have hs : (fun i x => F.decode ((targetTables T binary wire).vertex i x)) =
      extendedSignatures (fun j y => F.decode (T.vertex j y))
        (fun j a c => F.decode (binary j a c)) :=
    funext (fun i => funext (fun x => decode_extended F T binary i x))
  rw [hs]
  exact subdivision_partition_value r.val r.property
    (fun j y => F.decode (T.vertex j y)) (fun j a c => F.decode (T.edge j a c))
    (fun j a c => F.decode (binary j a c)) (fun a c => F.decode (wire a c)) hfuse

/-- The premise is the literal fixed local matrix identity. Both the graph
compiler and answer copier are concrete finite Boolean-stack programs. -/
def reduction
    (hfuse : ∀ j a c, (∑ uv : Bool×Bool,
      F.decode (wire a uv.1) * F.decode (binary j uv.1 uv.2) * F.decode (wire uv.2 c)) =
        F.decode (T.edge j a c)) :
    PolyTimeOracleReduction
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (RawClosedNetwork.validatedEncoding (s+b) 1 (targetArity s arity)) F.encoding
      (T.evaluate F) ((targetTables T binary wire).evaluate F) :=
  OracleOneQuery.of_eq (Compiler.computes s b arity) (identityComputes F.encoding)
    ((targetTables T binary wire).outputBound F) (T.evaluate F)
    (fun r => (evaluate_subdivision F T binary wire hfuse r).symm)

end
end Holant.Complexity.EdgeSubdivision
