import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePairedHardBridge
import Holant.Proofs.Hardness.GeneralEOUniversalSource

/-! Universal EO hardness of a genuine finite mixed-arity paired family
composes with the checked original-field native macro bridge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePairedHard
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace R
export EONegativePairReduction (signature family)
end R
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'
variable {t : ℕ} (row : Fin t→AnySignature AlgebraicComplex)
variable (N : (i : Fin t)→NativeAntiTargetSource.Output D.table (row i).1)
variable (form : ∀i,(fun z=>((N i).network.denote z : AlgebraicComplex))=(row i).2)

include form in
theorem signature_exact (i : Fin t) : R.signature (table target D row N) i=row i :=
  NoIPurePairedHardGraphs.signature_exact D.K D.table row N form i

include form in
theorem family_exact : R.family (table target D row N)=Set.range row :=
  NoIPurePairedHardGraphs.family_exact D.K D.table row N form

include form in
/-- A finite collection of genuine native EO graphs is compiled jointly. -/
theorem family (central : ∀i,Signature.CentralSupport (row i).2)
    (negative : ¬EOTract (preprocess (Set.range row))) : target.Hard := by
  have he : ∀i,Signature.CentralSupport (table target D row N i) := by
    intro i
    exact (congrArg (fun f : AnySignature AlgebraicComplex=>Signature.CentralSupport f.2)
      (signature_exact target D row N form i)).mpr (central i)
  have hn : ¬EOTract (preprocess (R.family (table target D row N))) := by
    rwa [family_exact target D row N form]
  intro α encoding count witness
  exact ⟨Programme.compose (GeneralEOUniversalSource.source (table target D row N) he hn witness)
    (back target D row N)⟩

section Pair
variable {m n : ℕ} (h : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
variable (Nh : NativeAntiTargetSource.Output D.table (m*2))
variable (Ng : NativeAntiTargetSource.Output D.table (n*2))
variable (fh : (fun z=>(Nh.network.denote z : AlgebraicComplex))=P.paired h)
variable (fg : (fun z=>(Ng.network.denote z : AlgebraicComplex))=P.paired g)

abbrev pairRow:=NoIPurePairedHardGraphs.pairRow h g
abbrev pairGraph:=NoIPurePairedHardGraphs.pairGraph D.K D.table h g Nh Ng

theorem pair_range : Set.range (pairRow h g)={⟨m*2,P.paired h⟩,⟨n*2,P.paired g⟩} :=
  NoIPurePairedHardGraphs.pair_range h g

include fh fg in
/-- The non-A and non-P witnesses may have different logical arities. -/
theorem two (badA : ¬Affine h) (badP : ¬Product g) : target.Hard := by
  apply family target D (pairRow h g) (pairGraph target D h g Nh Ng)
  · intro i
    fin_cases i
    · exact fh
    · exact fg
  · intro i
    fin_cases i
    · exact P.central h
    · exact P.central g
  · rw [pair_range]
    exact P.not_tract h g badA badP

include fh in
theorem singleton (badA : ¬Affine h) (badP : ¬Product h) : target.Hard :=
  two target D h h Nh Nh fh fh badA badP
end Pair


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePairedHard
end
