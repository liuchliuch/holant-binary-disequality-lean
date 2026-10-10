import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryIsotropicSource
import Holant.Tractable.Anchor

/-! Reflect the actual algebraic Z member into the source field, construct
its real cap with the isotropic unary, and install that whole-family adjoin
programme at unchanged original G. No independent unary is a premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryIsotropicLift
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace R
export GlobalCloseCompletionUnaryIsotropicSource (z determinant reflect independent output source)
end R
namespace L
export GlobalCloseCompletionUnaryLiteralSource (arity signatures)
end L
namespace U
export GeneralOddNonisotropicFrame (norm)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r s degree : ℕ} {b a : ℕ→ℕ}
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable (H : (i : Fin r)→Signature K (b i.val))

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin r=>
  RingHomRealization.mapAny K.val.toRingHom (⟨b i.val,H i⟩ : AnySignature K)

private theorem mapAny_injective : Function.Injective (RingHomRealization.mapAny K.val.toRingHom) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hn : n=m := congrArg Sigma.fst h
  subst m
  have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply congrArg (fun f : Signature K n=>(⟨n,f⟩ : AnySignature K))
  funext x
  exact K.val.injective (congrFun hf x)

theorem z_mapped : RingHomRealization.mapAny K.val.toRingHom (⟨2,R.z⟩ : AnySignature K)=⟨2,zAnchor⟩ := by
  apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [RingHomRealization.mapSignature,R.z,zAnchor,kernelSignature,diagonalKernel,h0,h1]

variable (hasZ : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈family K H)
include hasZ in
theorem z_exists : ∃j : Fin r,(⟨b j.val,H j⟩ : AnySignature K)=⟨2,R.z⟩ := by
  obtain ⟨j,hj⟩ := hasZ
  exact ⟨j,mapAny_injective K (hj.trans (z_mapped K).symm)⟩
def zLabel : Fin r := (z_exists K H hasZ).choose
theorem z_literal : (⟨b (zLabel K H hasZ).val,H (zLabel K H hasZ)⟩ : AnySignature K)=⟨2,R.z⟩ :=
  (z_exists K H hasZ).choose_spec

variable (N : Network K 1) (NL : Labelling N.shape r 1 b)
variable (exactN : LabelledNetwork.Exact H N NL) (ordinaryN : ∀e,N.edge e=Signature.equality)
def output := R.output H N NL exactN ordinaryN (zLabel K H hasZ) (z_literal K H hasZ)

theorem independent (nonzero : N.denote≠0) (isotropic : U.norm N.denote=0) :
    R.determinant N.denote (output K H hasZ N NL exactN ordinaryN).network.denote≠0 :=
  R.independent N (Network.corolla R.z) (Network.denote_corolla _) nonzero isotropic

theorem nonzero (first : N.denote≠0) (isotropic : U.norm N.denote=0) :
    (output K H hasZ N NL exactN ordinaryN).network.denote≠0 := by
  intro zero
  apply independent K H hasZ N NL exactN ordinaryN first isotropic
  simp [R.determinant,zero]

variable (F : FixedField K degree)
def source := R.source H N NL exactN ordinaryN (zLabel K H hasZ) (z_literal K H hasZ) F

section Original
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))

/-- The new literal unary is expanded by its one-edge graph; every old row
is preserved by the exact literal adjoin compiler. -/
def toOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (r+1) 1 (L.arity H (output K H hasZ N NL exactN ordinaryN))) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F
      (L.signatures F H (output K H hasZ N NL exactN ordinaryN))).evaluate F) (OriginalForestSource.value G) :=
  Programme.compose (source K H hasZ N NL exactN ordinaryN F) back

end Original


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryIsotropicLift
end
