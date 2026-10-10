import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZRootInverse
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZLift
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsAdjoin

/-! Prepare a ternary and a normalized physical binary square before the
inverse-edge chart. Both adjoins stay in the inverse producer's coefficient
field, and preserve its inverse row and every original ambient row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZPreparation
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization OrdinaryNegativeCubicGadgets
namespace R
export GlobalCloseCompletionSymmetricGHZRootInverse (Extension originalMacro)
end R
namespace Lft
export GlobalCloseCompletionSymmetricGHZLift (familyK familyL lift value)
end Lft
namespace A
export GlobalCloseCompletionIndependentPinsAdjoin
  (Output arity signatures source old old_literal newLabel new_literal lift)
end A
namespace I
export GlobalCloseCompletionSymmetricGHZInverseFinite (series series_value)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (N : Macro H 3) (C : A.Output H 2) (D : R.Extension L F H C)
local instance : Algebra ℚ D.K:=D.K.algebra'

abbrev field:=D.K
abbrev presentation:=D.presentation

theorem included : Lft.familyK L H⊆Lft.familyL D.K D.table := by
  rintro _ ⟨i,rfl⟩
  exact ⟨D.old i,D.old_literal i⟩

def ternary : Macro D.table 3:=Lft.lift L D.K H D.table (included L F H C D) N
def ternaryOutput : A.Output D.table 3:=
  ⟨(ternary L F H N C D).network,(ternary L F H N C D).labels,
    (ternary L F H N C D).exact,(ternary L F H N C D).edges⟩
def square : Macro D.table 2:=I.series D.table (R.originalMacro L F H C D) (R.originalMacro L F H C D)
def squareOutput : A.Output D.table 2:=
  ⟨(square L F H C D).network,(square L F H C D).labels,
    (square L F H C D).exact,(square L F H C D).edges⟩
theorem square_value : (square L F H C D).network.denote=binarySignature (D.original*D.original) :=
  I.series_value D.table _ _ _ _ D.original_form D.original_form

abbrev firstArity:=A.arity D.table (ternaryOutput L F H N C D)
abbrev firstTable:=A.signatures D.presentation D.table (ternaryOutput L F H N C D) 1
def liftedSquare : A.Output (firstTable L F H N C D) 2:=
  A.lift D.presentation D.table (ternaryOutput L F H N C D) 1 (squareOutput L F H C D)
abbrev arity:=A.arity (firstTable L F H N C D) (liftedSquare L F H N C D)
abbrev table:=A.signatures D.presentation (firstTable L F H N C D)
  (liftedSquare L F H N C D) (D.scalar^2)
def old (i : Fin r) : Fin (D.count+1+1):=
  A.old (firstTable L F H N C D) (A.old D.table (D.old i))
def hLabel : Fin (D.count+1+1):=A.old (firstTable L F H N C D) (A.newLabel D.table)
def inverseLabel : Fin (D.count+1+1):=A.old (firstTable L F H N C D) (A.old D.table D.label)
def gramLabel : Fin (D.count+1+1):=A.newLabel (firstTable L F H N C D)
def h : Signature D.K 3:=(ternary L F H N C D).network.denote
def gram : Binary (K:=D.K):=fun i j=>(D.scalar^2)⁻¹*(D.original*D.original) i j

theorem old_literal (i : Fin r) :
    RingHomRealization.mapAny D.K.subtype
      (⟨arity L F H N C D (old L F H N C D i).val,table L F H N C D (old L F H N C D i)⟩ : AnySignature D.K)=
      RingHomRealization.mapAny L.subtype (⟨b i.val,H i⟩ : AnySignature L) := by
  unfold old
  rw [A.old_literal,A.old_literal]
  exact D.old_literal i

theorem h_literal :
    (⟨arity L F H N C D (hLabel L F H N C D).val,table L F H N C D (hLabel L F H N C D)⟩ : AnySignature D.K)=
      ⟨3,h L F H N C D⟩ := by
  unfold hLabel
  rw [A.old_literal,A.new_literal]
  congr 1
  funext x
  exact div_one _

theorem h_value : RingHomRealization.mapSignature D.K.subtype (h L F H N C D)=
    RingHomRealization.mapSignature L.subtype N.network.denote :=
  Lft.value L D.K H D.table (included L F H C D) N

theorem inverse_literal :
    (⟨arity L F H N C D (inverseLabel L F H N C D).val,table L F H N C D (inverseLabel L F H N C D)⟩ : AnySignature D.K)=
      ⟨2,binarySignature D.inverse⟩ := by
  unfold inverseLabel
  rw [A.old_literal,A.old_literal]
  exact D.literal

theorem gram_literal :
    (⟨arity L F H N C D (gramLabel L F H N C D).val,table L F H N C D (gramLabel L F H N C D)⟩ : AnySignature D.K)=
      ⟨2,binarySignature (gram L F H C D)⟩ := by
  rw [gramLabel,A.new_literal]
  apply congrArg (fun f : Signature D.K 2=>(⟨2,f⟩ : AnySignature D.K))
  funext x
  change (square L F H C D).network.denote x / D.scalar^2=_
  rw [square_value]
  simp only [gram,binarySignature,div_eq_mul_inv,mul_comm]

def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (D.count+1+1) 1 (arity L F H N C D)) D.presentation.encoding
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    ((QuaternaryOrdinaryCompanion.tables D.presentation (table L F H N C D)).evaluate D.presentation)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) :=
  Programme.compose (A.source D.presentation (firstTable L F H N C D)
    (liftedSquare L F H N C D) (D.scalar^2) (pow_ne_zero _ D.nonzero))
    (Programme.compose (A.source D.presentation D.table (ternaryOutput L F H N C D) 1 one_ne_zero) D.source)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZPreparation
end
