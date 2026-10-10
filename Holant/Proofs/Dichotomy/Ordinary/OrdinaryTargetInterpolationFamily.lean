import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationRecovery

/-! Literal finite-family presentation for finite-target interpolation.
Old entries are unchanged; the new entry is precisely C+target·H. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationFamily
open Holant Holant.Algebraic Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation Holant.Complexity.BinaryInterpolation.Chains
open Holant.LocalDrafts.BinaryInterpolation Holant.Certificates.MatchingContractionClosure
namespace R
export OrdinaryTargetInterpolationRecovery (G kernels S slot value recovery controlled)
end R
namespace M
export OrdinaryTargetInterpolationMachine (Data Input inputEncoding queryEncoding)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ→ℕ}
variable {field : FixedField K n} {T : ExactSignatureTables n s b arity} (d : M.Data field T)
variable (C H : Binary (K:=K))
abbrev a := PhysicalQueries.A (s:=s) arity d.template
def signatures := RawPolynomial.pencil (R.S d) (R.slot d C) (R.slot d H) s d.target
def tables : ExactSignatureTables n (s+1) b (a d) where
  vertex i x := field.decode.symm (signatures d C H i x)
  edge := T.edge

theorem evaluate (r : M.Input d) : (tables d C H).evaluate field r=R.value d C H r := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [tables,LinearEquiv.apply_symm_apply]
  rfl

def old (i : Fin s) : Fin (s+1) := Fin.castAdd 1 i

theorem old_literal (i : Fin s) :
    (⟨a d (old i).val,signatures d C H (old i)⟩ : AnySignature K)=
      ⟨arity i.val,R.G (field:=field) (T:=T) i⟩ := by
  have hi : (old i).val≠s := Nat.ne_of_lt i.isLt
  have he : signatures d C H (old i)=R.S d (old i) := by
    funext x
    exact ite_eq_right hi
  rw [he]
  exact OriginalTables.tables_old d.template d.valid (R.G (field:=field) (T:=T))
      (R.kernels (field:=field) (T:=T)) i

theorem new_literal :
    (⟨a d s,signatures d C H PhysicalQueries.newLabel⟩ : AnySignature K)=
      ⟨2,binarySignature (C+d.target • H)⟩ := by
  have h := PhysicalQueries.signature_linear (R.slot d C PhysicalQueries.newLabel)
    (R.slot d H PhysicalQueries.newLabel) (binarySignature C) (binarySignature H)
    (OriginalTables.binarySlot_new d.template d.valid (R.G (field:=field) (T:=T))
      (R.kernels (field:=field) (T:=T)) d.binary C)
    (OriginalTables.binarySlot_new d.template d.valid (R.G (field:=field) (T:=T))
      (R.kernels (field:=field) (T:=T)) d.binary H) (1:K) d.target
  have he : signatures d C H PhysicalQueries.newLabel=
      R.slot d C PhysicalQueries.newLabel+d.target • R.slot d H PhysicalQueries.newLabel := by
    funext x
    exact ite_eq_left rfl
  rw [he]
  have hb : binarySignature C+d.target • binarySignature H=binarySignature (C+d.target • H) := by
    funext x
    rfl
  rw [←hb]
  simpa only [one_smul] using h

variable (hchain : ∀ k : ℕ,
    ((explicitTemplate s d.edge.val k).network
      (explicitTemplate_wellFormed (PhysicalQueries.A (s:=s) arity d.template) PhysicalQueries.newLabel
        (PhysicalQueries.new_arity (s:=s) arity d.template d.binary) d.edge k)
      (R.S d) (R.kernels (field:=field) (T:=T))).denote =
      binarySignature (d.gamma^(k+1) • (C+d.rho^(k+1) • H)))

def controlled (hg : d.gamma≠0)
    (hi : ∀m,Function.Injective (OrdinaryNegativeBinaryUnsignedInterpolationFormulas.nodes d.rho m)) :
    LengthControlledOracleReduction (M.inputEncoding d) field.encoding
      (M.queryEncoding (s:=s) (b:=b) (arity:=arity)) field.encoding
      ((tables d C H).evaluate field) (T.evaluate field) := by
  have eqn : (tables d C H).evaluate field=R.value d C H := funext (evaluate d C H)
  rw [eqn]
  exact R.controlled d C H hchain hg hi

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationFamily
end
