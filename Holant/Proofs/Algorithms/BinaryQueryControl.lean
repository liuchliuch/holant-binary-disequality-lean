import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Proofs.BinaryInterpolation.FieldSource


namespace Holant.LocalDrafts.MainChain.BinaryQueryControl
open Computability Holant.Algebraic Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.Complexity.BinaryInterpolation
open Holant.LocalDrafts.BinaryInterpolation
open Holant.Complexity.OracleBatch
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature ℂ (arity i.val))
variable (halg : ∀ i x, IsAlgebraic ℚ (G i x))
variable {B : Binary (K:=ℂ)} (M : AlgebraicSource.Macro G B)
variable (p : AlgebraicSource.Pencil M.binary)

def targetOutput : PolynomialOutputBound
    (FieldSource.targetEncoding (s:=s) (arity:=arity)) (FieldSource.outputEncoding G halg M p)
    (AlgebraicSource.CommonField.targetValue G M.binary p) := by
  have h := (FieldSource.targetTables G halg M p).outputBound (FieldSource.fixedField G halg M p)
  have he : (FieldSource.targetTables G halg M p).evaluate (FieldSource.fixedField G halg M p) =
      AlgebraicSource.CommonField.targetValue G M.binary p :=
    funext (FieldSource.target_evaluate G halg M p)
  rw [he] at h
  exact h

def controlled : LengthControlledOracleReduction
    (FieldSource.inputEncoding (s:=s) (arity:=arity)) (FieldSource.outputEncoding G halg M p)
    (FieldSource.targetEncoding (s:=s) (arity:=arity)) (FieldSource.outputEncoding G halg M p)
    (AlgebraicSource.CommonField.sourceValue G M.binary p)
    (AlgebraicSource.CommonField.targetValue G M.binary p) where
  reduction := FieldSource.reduction G halg M p
  targetOutput := targetOutput G halg M p
  queryBound := (MachineCapstone.pre (FieldSource.data G halg M p)).outputBound.bound
  safeQuery oracle ho r t c hr hq := by
    obtain ⟨n,_,htrace⟩ := FieldSource.execution G halg M p oracle ho r
    have hm := TraceQueryControl.transcript_member htrace t c hr hq
    obtain ⟨q,hmem,he⟩ := List.mem_map.mp hm
    refine ⟨q,he.symm,?_⟩
    have hl := member_length_le _ _ hm
    have hp := (query_context_length_le
      (MachineCapstone.pre (FieldSource.data G halg M p)) (FieldSource.asMacroInput G M r)).1
    exact hl.trans hp

/-- This is machine integration only. The downstream machine must already
exist with the exact intermediate oracle type; no hardness result is inferred
from accepting such a machine as an argument. -/
def thenReduction {α β : Type} {ea : Encoding α Bool} {eb : Encoding β Bool} {f : α → β}
    (next : PolyTimeOracleReduction
      (FieldSource.targetEncoding (s:=s) (arity:=arity)) (FieldSource.outputEncoding G halg M p)
      ea eb (AlgebraicSource.CommonField.targetValue G M.binary p) f) :
    PolyTimeOracleReduction
      (FieldSource.inputEncoding (s:=s) (arity:=arity)) (FieldSource.outputEncoding G halg M p)
      ea eb (AlgebraicSource.CommonField.sourceValue G M.binary p) f :=
  (controlled G halg M p).compose next

end
end Holant.LocalDrafts.MainChain.BinaryQueryControl
