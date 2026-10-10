import Holant.OpenNetworkComposition.Closure
import Holant.Dihedral.CompatibleClosure.ActualReindex
import Mathlib.Data.Finset.Basic

/-! Literal I vertices on native X edges implement arbitrary original-port
bit translations. The finite induction splices disjoint actual gadgets and
keeps the entire old tensor and coefficient field unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2BitTranslateActual
open Holant
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [CommSemiring K] {n : ℕ}

def identity : Signature K 2 := fun x=>Signature.equality (x 0) (x 1)
def toggle (s : Finset (Fin n)) (f : Signature K n) : Signature K n :=
  fun x=>f (fun i=>if i∈s then !(x i) else x i)

theorem splice_identity (f : Signature K n) (i : Fin n) :
    OpenNetworkComposition.spliceTensor f identity i=fun x=>f (Function.update x i (!(x i))) := by
  funext x
  unfold OpenNetworkComposition.spliceTensor
  cases hi : x i <;> simp [identity,Signature.equality,Signature.disequality,hi]

variable (F : SignatureFamily K)
variable (hI : (⟨2,identity⟩ : AnySignature K)∈F)

include hI in
theorem toggle_actual (f : Signature K n) (hf : Gadget.Realizes F .disequality f) (s : Finset (Fin n)) :
    Gadget.Realizes F .disequality (toggle s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : toggle (∅ : Finset (Fin n)) f=f := by
      funext x
      apply congrArg f
      funext i
      simp [toggle]
    rw [h]
    exact hf
  | @insert i s hi ih =>
    have h := OpenNetworkComposition.realizes_splice F (toggle s f) identity ih
      (Gadget.realizes_of_mem F .disequality identity hI) i
    rw [splice_identity] at h
    convert h using 1
    funext x
    apply congrArg f
    funext j
    by_cases hj : j=i
    · subst j
      simp [toggle,hi]
    · simp [toggle,Finset.mem_insert,Function.update,hj]

def translate (f : Signature K n) (a : Fin n→Bool) : Signature K n :=
  fun x=>f (fun i=>x i ^^ a i)

include hI in
theorem translate_actual (f : Signature K n) (hf : Gadget.Realizes F .disequality f) (a : Fin n→Bool) :
    Gadget.Realizes F .disequality (translate f a) := by
  have h := toggle_actual F hI f hf (Finset.univ.filter fun i=>a i=true)
  convert h using 1
  funext x
  apply congrArg f
  funext i
  cases hi : a i <;> simp [translate,toggle,hi]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2BitTranslateActual
end
