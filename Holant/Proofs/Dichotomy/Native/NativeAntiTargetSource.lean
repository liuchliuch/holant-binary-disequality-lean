import Holant.Proofs.Dichotomy.Native.NativeTableBase
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetOutput
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetAdjoin
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetAdjoin
import Holant.Proofs.Algorithms.QuaternaryOrdinaryCompanion

/-! Literal antidiagonal interpolation on arbitrary actual native-X graphs,
without any supplied identity vertex. All original table rows and the exact
finite coefficient field survive the controlled source extension. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetSource
open Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.BinaryInterpolation
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace I
export NativeAntiTargetAdjoin (data signatures tables new_literal controlled)
end I
namespace R
export OrdinaryTargetInterpolationRecovery (G kernels)
end R
namespace D
export NativeAntiTargetAlgebra (anti)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)

variable (N : Output H 2) (u v target : K)

abbrev arity := PhysicalQueries.A (s:=s) a N.template
abbrev table := I.signatures F (base H F) N.template N.labels.wellFormed rfl (0 : Fin 1) u v target
abbrev data := I.data F (base H F) N.template N.labels.wellFormed rfl (0 : Fin 1) u v target

def old (i : Fin s) : Fin (s+1) := Fin.castAdd 1 i

theorem old_literal (i : Fin s) :
    (⟨arity H N (old i).val,table H F N u v target (old i)⟩ : AnySignature K)=⟨a i.val,H i⟩ := by
  refine (OrdinaryTargetInterpolationFamily.old_literal (data H F N u v target)
    (D.anti 1 0) (D.anti 0 1) i).trans ?_
  apply congrArg (fun f : Signature K (a i.val)=>(⟨a i.val,f⟩ : AnySignature K))
  funext x
  exact F.decode.apply_symm_apply _

def label : Fin (s+1) := ⟨s,Nat.lt_succ_self _⟩
theorem literal :
    (⟨arity H N (label (s:=s)).val,table H F N u v target label⟩ : AnySignature K)=
      ⟨2,binarySignature (D.anti 1 target)⟩ :=
  I.new_literal F (base H F) N.template N.labels.wellFormed rfl (0 : Fin 1) u v target

theorem ordinary : R.kernels (field:=F) (T:=base H F) (0 : Fin 1)=Signature.disequality := by
  funext x y
  exact F.decode.apply_symm_apply _

theorem macro_exact (form : N.network.denote=binarySignature (D.anti u v)) :
    (⟨N.template.boundary,(N.template.network N.labels.wellFormed
      (R.G (field:=F) (T:=base H F)) (R.kernels (field:=F) (T:=base H F))).denote⟩ : AnySignature K)=
      ⟨2,binarySignature (D.anti u v)⟩ := by
  have hg : R.G (field:=F) (T:=base H F)=H := by
    funext i x
    exact F.decode.apply_symm_apply _
  have he : R.kernels (field:=F) (T:=base H F)=(fun _ : Fin 1=>Signature.disequality) := by
    funext i
    exact Subsingleton.elim i 0 ▸ ordinary H F
  rw [hg,he,template_exact,form]
  rfl

def source (hu : u≠0) (hv : v≠0) (infinite : ∀n : ℕ,0<n→(v/u)^n≠1)
    (form : N.network.denote=binarySignature (D.anti u v)) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (s+1) 1 (arity H N)) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
      ((base (table H F N u v target) F).evaluate F)
      ((base H F).evaluate F) :=
  I.controlled F (base H F) N.template N.labels.wellFormed rfl (0 : Fin 1) u v target
    (ordinary H F) (macro_exact H F N u v form) hu hv infinite

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetSource
end
