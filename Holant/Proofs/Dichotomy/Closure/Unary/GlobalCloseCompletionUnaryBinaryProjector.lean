import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryPencil
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationChain

/-! A genuine two-sided binary endpoint with infinite eigenvalue ratio
supplies its perpendicular rank-one projector through the checked positive
chain compiler. The interpolation stays in the unchanged original ordinary
coordinates and preserves the full old dictionary and coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryProjector
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation
open Holant.Complexity.BinaryInterpolation.Chains hiding binarySignature
open Holant.LocalDrafts.BinaryInterpolation Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace X
export NoXOrdinaryGraphAdjoin (Output baseTables template macro_exact)
end X
namespace U
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicFrame (norm chart)
end U
namespace E
export GlobalCloseCompletionUnaryHigherEq4 (endpoint)
end E
namespace P
export GlobalCloseCompletionUnaryBinarySpectrum (projector)
export GlobalCloseCompletionUnaryBinaryPencil (pencil)
end P
namespace R
export OrdinaryTargetInterpolationRecovery (G kernels S)
end R
namespace F
export OrdinaryTargetInterpolationFamily (signatures tables old_literal new_literal controlled)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {r degree : ℕ} {b : ℕ→ℕ}
variable (field : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))
variable (N : X.Output H 2) (u : Signature K 1) (A B : K)

abbrev base := X.baseTables field H
abbrev template := X.template H N
def data : OrdinaryTargetInterpolationMachine.Data field (base field H) where
  template := template H N
  valid := N.labels.wellFormed
  binary := rfl
  edge := 0
  gamma := B/U.norm u
  rho := A/B
  target := 0
abbrev arity := OrdinaryTargetInterpolationFamily.a (data field H N u A B)
abbrev signatures := F.signatures (data field H N u A B) (P.projector u true) (P.projector u false)
abbrev tables := F.tables (data field H N u A B) (P.projector u true) (P.projector u false)

variable (hu : U.norm u≠0) (ha : A≠0) (hb : B≠0)
variable (form : U.chart u N.network.denote=E.endpoint 2 A B)
include hu hb form in
theorem chain (k : ℕ) :
    ((explicitTemplate r 0 k).network
      (explicitTemplate_wellFormed (PhysicalQueries.A (s:=r) b (template H N)) PhysicalQueries.newLabel
        (PhysicalQueries.new_arity (s:=r) b (template H N) rfl) (0 : Fin 1) k)
      (R.S (data field H N u A B))
      (R.kernels (field:=field) (T:=base field H))).denote=
      binarySignature ((B/U.norm u)^(k+1) • (P.projector u true+(A/B)^(k+1) • P.projector u false)) := by
  have macroValue : (⟨(template H N).boundary,((template H N).network N.labels.wellFormed
      (R.G (field:=field) (T:=base field H)) (R.kernels (field:=field) (T:=base field H))).denote⟩ : AnySignature K)=
      ⟨2,binarySignature (binaryMatrix N.network.denote)⟩ := by
    apply congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K))
    exact (X.macro_exact field H N).trans (binarySignature_binaryMatrix _).symm
  have h := OrdinaryTargetInterpolationChain.explicitTemplate_denote_I
    (PhysicalQueries.A (s:=r) b (template H N)) PhysicalQueries.newLabel
    (PhysicalQueries.new_arity (s:=r) b (template H N) rfl) (0 : Fin 1) k (binaryMatrix N.network.denote)
    (OriginalTables.tables (template H N) N.labels.wellFormed
      (R.G (field:=field) (T:=base field H)) (R.kernels (field:=field) (T:=base field H)))
    (R.kernels (field:=field) (T:=base field H))
    ((OriginalTables.tables_new (template H N) N.labels.wellFormed
      (R.G (field:=field) (T:=base field H)) (R.kernels (field:=field) (T:=base field H))).trans macroValue)
    (by funext p q;exact field.decode.apply_symm_apply (Signature.equality p q))
  exact h.trans (congrArg binarySignature (P.pencil u hu N.network.denote A B hb form (k+1)))

theorem old_literal (i : Fin r) :
    (⟨arity field H N u A B (Fin.castAdd 1 i).val,signatures field H N u A B (Fin.castAdd 1 i)⟩ : AnySignature K)=
      ⟨b i.val,H i⟩ := by
  have h := F.old_literal (data field H N u A B) (P.projector u true) (P.projector u false) i
  refine h.trans ?_
  apply congrArg (fun f : Signature K (b i.val)=>(⟨b i.val,f⟩ : AnySignature K))
  funext x
  exact field.decode.apply_symm_apply (H i x)

theorem new_literal :
    (⟨arity field H N u A B r,signatures field H N u A B ⟨r,Nat.lt_succ_self _⟩⟩ : AnySignature K)=
      ⟨2,binarySignature (P.projector u true)⟩ := by
  have h := F.new_literal (data field H N u A B) (P.projector u true) (P.projector u false)
  refine h.trans ?_
  apply congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K))
  funext x
  simp [data,Chains.binarySignature,
    Holant.Certificates.MatchingContractionClosure.binarySignature]

def controlled (infinite : ∀k : ℕ,0<k→(A/B)^k≠1) : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (r+1) 1 (arity field H N u A B)) field.encoding
    (RawClosedNetwork.validatedEncoding r 1 b) field.encoding
    ((QuaternaryOrdinaryCompanion.tables field (signatures field H N u A B)).evaluate field)
    ((base field H).evaluate field) :=
  F.controlled (data field H N u A B) (P.projector u true) (P.projector u false)
    (chain field H N u A B hu hb form) (div_ne_zero hb hu)
    (OrdinaryNegativeBinaryUnsignedInterpolationFormulas.nodes_injective (A/B) (div_ne_zero ha hb) infinite)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryProjector
end
