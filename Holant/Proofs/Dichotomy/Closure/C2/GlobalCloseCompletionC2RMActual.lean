import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2BitTranslateActual
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2ReedMuller
import Holant.ReedMuller.TwoChart.ContextRealization

/-! The proved RM8 coefficient normal form yields a genuine native network
for a nonzero scalar multiple of literal RM. Only original-port reindexing
and actual retained I legs are used; its scalar is recovered in the old field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RMActual
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Certificates.MatchingContractionClosure
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CoefficientAtlas
namespace B
export GlobalCloseCompletionC2BitTranslateActual (identity translate translate_actual)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K]

def rm : Signature K 8 := fun x=>if (fun p=>boolEquiv (x p))∈code then 1 else 0

theorem bit_cancel (b : Bool) (z : ZMod 2) : boolEquiv (b ^^ boolEquiv.symm z)+z=boolEquiv b := by
  cases b <;> fin_cases z <;> decide

theorem recover (phi : K→+*ℂ) (f : Signature K 8) (e : Equiv.Perm (Fin 8))
    (a : BinaryVector 8) (c : ℂ) (hc : c≠0)
    (equation : ∀x,phi (f x)=if (fun p=>boolEquiv (x (e p)))+a∈code then c else 0) :
    ∃d : K,d≠0 ∧ ∀x,f x=if (fun p=>boolEquiv (x (e p)))+a∈code then d else 0 := by
  let x0 : Fin 8→Bool := fun i=>boolEquiv.symm (a (e.symm i))
  have zero : (fun p=>boolEquiv (x0 (e p)))+a=0 := by
    funext p
    change boolEquiv (boolEquiv.symm (a (e.symm (e p))))+a p=0
    rw [Equiv.symm_apply_apply,Equiv.apply_symm_apply]
    exact CharTwo.add_self_eq_zero (a p)
  have image : phi (f x0)=c := by
    rw [equation,zero,if_pos (Submodule.zero_mem code)]
  refine ⟨f x0,?_,?_⟩
  · intro h
    exact hc (image.symm.trans (by rw [h,map_zero]))
  · intro x
    apply phi.injective
    rw [equation]
    by_cases hx : (fun p=>boolEquiv (x (e p)))+a∈code
    · rw [if_pos hx,if_pos hx]
      exact image.symm
    · rw [if_neg hx,if_neg hx,map_zero]

variable (F : SignatureFamily K)
variable (hI : (⟨2,B.identity⟩ : AnySignature K)∈F)

include hI in
theorem actual_from_coefficients (f : Signature K 8) (actual : Gadget.Realizes F .disequality f)
    (e : Equiv.Perm (Fin 8)) (a : BinaryVector 8) (c : K)
    (form : ∀x,f x=if (fun p=>boolEquiv (x (e p)))+a∈code then c else 0) :
    Gadget.Realizes F .disequality (c • rm) := by
  have reordered := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality f actual e
  have shifted := B.translate_actual F hI (Tensor.reindex e.symm f) reordered (fun i=>boolEquiv.symm (a i))
  convert shifted using 1
  funext x
  simp only [B.translate,Tensor.reindex,Equiv.symm_apply_apply]
  rw [form]
  have words : (fun p=>boolEquiv (x (e.symm (e p)) ^^ boolEquiv.symm (a (e.symm (e p)))))+a=
      (fun p=>boolEquiv (x p)) := by
    funext p
    simp only [Pi.add_apply,Equiv.symm_apply_apply]
    exact bit_cancel _ _
  rw [words]
  simp only [Pi.smul_apply,smul_eq_mul,rm]
  split_ifs <;> simp

theorem rm_algebraic : (rm (K:=AlgebraicComplex))=Holant.ReedMuller.TwoChart.algebraicRM := by
  funext x
  apply Subtype.ext
  have words : (fun p=>boolEquiv (x p))=(fun p=>bit (x p)-(0 : BinaryVector 8) p) := by
    funext p
    change (if x p then 1 else 0)=(if x p then 1 else 0)-0
    rw [sub_zero]
  simp only [rm,Holant.ReedMuller.TwoChart.algebraicRM,rmCore,flatSignature,Units.val_one]
  rw [words]
  split_ifs <;> rfl

variable [NumberField K]

theorem current_actual (torsion : ResidualTorsion F) (retainedI : RetainsIdentity F)
    (cardTwo : Nat.card (completeGroup F torsion)=2) (phi : K→+*ℂ)
    (f : Signature K 8) (retained : (⟨8,f⟩ : AnySignature K)∈F)
    (prime : Prime (⟨8,f⟩ : AnySignature K))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    ∃c : K,c≠0 ∧ Gadget.Realizes F .disequality (c • rm) := by
  obtain ⟨e,c,a,hc,eqn⟩ := GlobalCloseCompletionC2ReedMuller.current_prime_exact_code
    F torsion retainedI cardTwo phi f prime stable
  obtain ⟨d,hd,hf⟩ := recover phi f e a c hc eqn
  have identity : (⟨2,B.identity⟩ : AnySignature K)∈F := by
    exact retainedI
  exact ⟨d,hd,actual_from_coefficients F identity f (Gadget.realizes_of_mem F .disequality f retained) e a d hf⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RMActual
end
