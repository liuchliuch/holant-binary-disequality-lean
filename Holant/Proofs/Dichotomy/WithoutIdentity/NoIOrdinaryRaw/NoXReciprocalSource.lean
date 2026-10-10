import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationAdjoin
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! A finite-target diagonal extension of the actual ordinary source. The
new row is backed by the checked positive-chain interpolation programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXReciprocalSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.BinaryInterpolation
namespace A
export OrdinaryTargetInterpolationAdjoin (data signatures tables controlled new_literal)
end A
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal)
end D
namespace X
export NoXOrdinaryGraphAdjoin (Output baseTables template macro_exact)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (graph : X.Output src.H 2) (c d target : src.K)
abbrev base := X.baseTables src.F src.H
abbrev template := X.template src.H graph
abbrev interpolation := A.data src.F (base G src) (template G src graph)
  graph.labels.wellFormed rfl (0 : Fin 1) c d target
abbrev arity := OrdinaryTargetInterpolationFamily.a (interpolation G src graph c d target)
abbrev signatures := A.signatures src.F (base G src) (template G src graph)
  graph.labels.wellFormed rfl (0 : Fin 1) c d target
abbrev tables := A.tables src.F (base G src) (template G src graph)
  graph.labels.wellFormed rfl (0 : Fin 1) c d target

theorem old_literal (i : Fin src.size) :
    (⟨arity G src graph c d target (Fin.castAdd 1 i).val,
      signatures G src graph c d target (Fin.castAdd 1 i)⟩ : AnySignature src.K)=
    ⟨src.b i.val,src.H i⟩ := by
  have h := OrdinaryTargetInterpolationFamily.old_literal
    (interpolation G src graph c d target) (D.diagonal 1 0) (D.diagonal 0 1) i
  refine h.trans ?_
  apply congrArg (fun f : Signature src.K (src.b i.val) => (⟨src.b i.val,f⟩ : AnySignature src.K))
  funext x
  exact src.F.decode.apply_symm_apply (src.H i x)

theorem ordinary_tables : QuaternaryOrdinaryCompanion.tables src.F
    (signatures G src graph c d target)=tables G src graph c d target := by
  rfl

variable (denote : graph.network.denote=binarySignature (D.diagonal c d))
variable (hc : c≠0) (hd : d≠0) (infinite : ∀k : ℕ,0<k→(d/c)^k≠1)

def controlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (src.size+1) 1 (arity G src graph c d target)) src.F.encoding
    (RawClosedNetwork.validatedEncoding src.size 1 src.b) src.F.encoding
    ((QuaternaryOrdinaryCompanion.tables src.F (signatures G src graph c d target)).evaluate src.F)
    ((base G src).evaluate src.F) := by
  rw [ordinary_tables]
  apply A.controlled src.F (base G src) (template G src graph)
    graph.labels.wellFormed rfl (0 : Fin 1) c d target
  · funext x y
    exact src.F.decode.apply_symm_apply (Signature.equality x y)
  · apply congrArg (fun f : Signature src.K 2 => (⟨2,f⟩ : AnySignature src.K))
    exact (X.macro_exact src.F src.H graph).trans denote
  · exact hc
  · exact hd
  · exact infinite

def data : NoIOrdinaryRaw.GenericOrdinarySource.Data G where
  K := src.K
  degree := src.degree
  F := src.F
  size := src.size+1
  b := arity G src graph c d target
  H := signatures G src graph c d target
  e := Fin.castAdd 1 src.e
  p b := Fin.castAdd 1 (src.p b)
  he := (old_literal G src graph c d target src.e).trans src.he
  hp b := (old_literal G src graph c d target (src.p b)).trans (src.hp b)
  toOriginal := Programme.compose
    (controlled G src graph c d target denote hc hd infinite) src.toOriginal


theorem new_literal :
    (⟨(data G src graph c d target denote hc hd infinite).b src.size,
      (data G src graph c d target denote hc hd infinite).H
        (⟨src.size,Nat.lt_succ_self _⟩ : Fin (src.size+1))⟩ : AnySignature src.K)=
    ⟨2,binarySignature (D.diagonal 1 target)⟩ :=
  A.new_literal src.F (base G src) (template G src graph)
    graph.labels.wellFormed rfl (0 : Fin 1) c d target

theorem old_included : NoIOrdinaryRaw.GenericOrdinarySource.family G src ⊆
    NoIOrdinaryRaw.GenericOrdinarySource.family G (data G src graph c d target denote hc hd infinite) := by
  rintro f ⟨i,rfl⟩
  refine ⟨Fin.castAdd 1 i,?_⟩
  exact congrArg (RingHomRealization.mapAny src.K.subtype)
    (old_literal G src graph c d target i)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoXReciprocalSource
end
