import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Closed
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryCharts
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopOrdinarySource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryIsotropicLift

/-! Actual C2 current q4 consumption, with no parity premise. The complete
ordinary K-coordinate table and original-G reduction are retained, and the
checked eight-space cover selects a real port/Z chart of the original row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2QuaternaryCurrent
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace S
export GlobalCloseCompletionStopOrdinarySource (field table family presentation retained_literal z_member toOriginal)
end S
namespace C
export GlobalCloseCompletionC2Q4UnionCurrent (word tensor coefficients tensor_coefficients)
end C
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def values (f : Signature AlgebraicComplex 4) : Fin 8→AlgebraicComplex := fun i=>f (C.word i)

theorem algebraic_tensor (f : Signature AlgebraicComplex 4) (comp : ∀x,f x=f (fun i=>!(x i))) : C.tensor (values f)=f := by
  have h := C.tensor_coefficients (fun x=>(f x:ℂ)) (fun x=>congrArg Subtype.val (comp x))
  funext x
  apply Subtype.ext
  have hx := congrFun h x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simpa only [C.tensor,C.coefficients,values,h0,h1,h2,h3] using hx

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
local instance : Algebra ℚ (S.field G P) := (S.field G P).algebra'
variable (torsion : ResidualTorsion P.family) (hI : RetainsIdentity P.family)
variable (cardTwo : Nat.card (completeGroup P.family torsion)=2)
variable (f : Signature (OI.K G) 4) (retained : (⟨4,f⟩ : AnySignature (OI.K G))∈P.family)
variable (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)

include retained in
theorem source_row : ∃N : Macro (S.table G P) 4,
    RingHomRealization.mapSignature (S.field G P).subtype N.network.denote=
      sourceKBasis.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f) := by
  obtain ⟨i,literal⟩ := retained
  have member : (⟨4,sourceKBasis.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f)⟩ : AnySignature AlgebraicComplex)∈S.family G P :=
    ⟨i,S.retained_literal G P i f literal⟩
  have mappedMember : (⟨4,sourceKBasis.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f)⟩ : AnySignature AlgebraicComplex)∈
      RingHomRealization.mapFamily (S.field G P).subtype (Set.range fun j : Fin P.count=>(⟨P.arity j.val,S.table G P j⟩ : AnySignature (S.field G P))) := by
    obtain ⟨j,hj⟩ := member
    exact ⟨⟨P.arity j.val,S.table G P j⟩,⟨j,rfl⟩,hj⟩
  obtain ⟨q,hq,equation⟩ := RingHomDescent.vertex_preimage (K:=S.field G P) (L:=AlgebraicComplex)
    (F:=Set.range fun j : Fin P.count=>(⟨P.arity j.val,S.table G P j⟩ : AnySignature (S.field G P)))
    (n:=4) (S.field G P).subtype
    (sourceKBasis.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f)) mappedMember
  obtain ⟨j,hj⟩ := hq
  exact ⟨Macro.row j q hj,by rw [Macro.row_denote];exact equation⟩

theorem source_z : ∃z : Fin P.count,
    (⟨P.arity z.val,S.table G P z⟩ : AnySignature (S.field G P))=⟨2,fun x=>T.Z (x 0) (x 1)⟩ := by
  exact GlobalCloseCompletionUnaryIsotropicLift.z_exists (S.field G P) (S.table G P) (S.z_member G P)

include torsion hI cardTwo retained stable in
theorem classified :
    Affine (sourceKBasis.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f)) ∨
      Tract (S.family G P) ∨ PaperControlledHardness.Original G := by
  let g := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f
  let v := values g
  let phi : OI.K G→+*ℂ := (algebraicClosure ℚ ℂ).subtype.comp (ClosureSourceRows.embedding G)
  have accepted : GlobalCloseCompletionC2Q4Union.Accepted (fun i=>(v i:ℂ)) :=
    GlobalCloseCompletionC2Q4Closed.current_accepted P.family torsion hI cardTwo phi f stable
  have comp : ∀x,g x=g (fun i=>!(x i)) := fun x=>congrArg (ClosureSourceRows.embedding G)
    (GlobalCloseCompletionC2CurrentComplement.current_complement P.family torsion hI cardTwo f stable x)
  obtain ⟨N,equation⟩ := source_row G P f retained
  obtain ⟨z,zLiteral⟩ := source_z G P
  have form : RingHomRealization.mapSignature (S.field G P).subtype N.network.denote=sourceKBasis.action (C.tensor v) := by
    rw [algebraic_tensor g comp]
    exact equation
  have h := PaperControlled.C2OrdinaryCharts.classified G (S.field G P) (S.presentation G P)
    (S.table G P) (S.toOriginal G P) z zLiteral N v form accepted
  rcases h with affine|tract|hard
  · exact Or.inl (equation ▸ affine)
  · exact Or.inr (Or.inl tract)
  · exact Or.inr (Or.inr hard)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2QuaternaryCurrent
end
