import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramAllPairs
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2BitTranslateActual
import Holant.Tractable.AffineOperations

/-! Actual portwise Boolean translations preserve genuine tensor primality
and preserve the native Affine class. No independent unary resource is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinBitTranslate
open Holant Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace B
export GlobalCloseCompletionC2BitTranslateActual (translate translate_actual)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] {n : ℕ}

theorem xor_twice (a b : Bool) : ((a ^^ b) ^^ b) = a := by cases a <;> cases b <;> rfl

theorem involutive (f : Signature K n) (mask : Fin n→Bool) :
    B.translate (B.translate f mask) mask=f := by
  funext x
  apply congrArg f
  funext i
  change ((x i ^^ mask i) ^^ mask i) = x i
  exact xor_twice _ _

theorem prime (f : Signature K n) (hf : Prime (⟨n,f⟩ : AnySignature K)) (mask : Fin n→Bool) :
    Prime (⟨n,B.translate f mask⟩ : AnySignature K) := by
  constructor
  · intro zero
    apply hf.1
    have h := congrArg (fun g=>B.translate g mask) zero
    rw [involutive] at h
    exact h
  · rintro ⟨a,b,⟨split⟩⟩
    apply hf.2
    refine ⟨⟨a.1,B.translate a.2 (fun i=>mask (split.ports (.inl i)))⟩,
      ⟨b.1,B.translate b.2 (fun i=>mask (split.ports (.inr i)))⟩,
      ⟨⟨split.left_pos,split.right_pos,split.ports,split.scale,?_⟩⟩⟩
    funext x
    have h := congrFun split.equation (fun i=>x i ^^ mask i)
    have cancel : (fun i=>(x i ^^ mask i) ^^ mask i)=x := by
      funext i
      cases x i <;> cases mask i <;> rfl
    simp only [B.translate] at h
    rw [cancel] at h
    exact h

theorem affine_map (mask : Fin n→Bool) :
    TwoTranslate.IsAffineMap (fun x : Fin n→Bool=>fun i=>x i ^^ mask i) := by
  intro x y
  funext i
  simp only [AffinePhase.xor,AffinePhase.origin]
  cases x i <;> cases y i <;> cases mask i <;> rfl

theorem affine (f : Signature AlgebraicComplex n) (hf : Affine f) (mask : Fin n→Bool) :
    Affine (B.translate f mask) := hf.precompose _ (affine_map mask)

theorem affine_iff (f : Signature AlgebraicComplex n) (mask : Fin n→Bool) :
    Affine (B.translate f mask) ↔ Affine f :=
  ⟨fun h=>by simpa only [involutive] using affine _ h mask,fun h=>affine f h mask⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinBitTranslate
end
