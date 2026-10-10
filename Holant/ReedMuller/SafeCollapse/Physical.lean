import Holant.ReedMuller.SafeCollapse.Diagonal
import Holant.Certificates.TwelveLoops.Transfers
import Holant.Observability.Links

/-! Native-X provenance of the first-port operation, and actual safe binary
representatives rather than an assumed abstract supply of transfer matrices. -/
namespace Holant.ReedMuller.SafeCollapse
open Holant Holant.ReedMuller.CoefficientAtlas
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def binarySignature (B : Mat) : Signature ℂ 2 := fun x => B (x 0) (x 1)
def transfer (B : Mat) : Mat := Kernel.mul B Signature.disequality

theorem coordinateAction_head_general {n : ℕ} (A : Fin (n+1) → Mat)
    (f : Signature ℂ (n+1)) (a : Bool) (x : Fin n → Bool) :
    Signature.coordinateAction A f (Fin.cons a x)=
      ∑ b : Bool,A 0 a b * Signature.coordinateAction (fun j => A j.succ) (Signature.pin f b) x := by
  simp [Signature.coordinateAction,sum_words_succ,Fin.prod_univ_succ,Signature.pin,
    Finset.mul_sum,mul_assoc]

theorem word_cons_tail {n : ℕ} (x : Fin (n+1) → Bool) : Fin.cons (x 0) (Fin.tail x)=x := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  rfl

theorem update_first {n : ℕ} (x : Fin (n+1) → Bool) (a : Bool) :
    Function.update x 0 a=Fin.cons a (Fin.tail x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp
    rfl

theorem onePort_first {n : ℕ} (f : Signature ℂ (n+1)) (T : Mat) (x : Fin (n+1) → Bool) :
    onePort f T 0 x=∑ a : Bool,T (x 0) a*f (Function.update x 0 a) := by
  conv_lhs => rw [←word_cons_tail x]
  rw [onePort,coordinateAction_head_general]
  simp only [ite_true]
  have hA : (fun j : Fin n => if j.succ=(0:Fin (n+1)) then T else Signature.equality)=
      (fun _ => Signature.equality) := by funext j;simp
  rw [hA]
  simp only [Signature.coordinateAction_equality,Signature.pin,update_first]

theorem onePort_eq_splice {n : ℕ} (f : Signature ℂ (n+1)) (B : Mat) :
    onePort f (transfer B) 0=OpenNetworkComposition.spliceTensor f (binarySignature B) 0 := by
  funext x
  rw [onePort_first]
  simp [transfer,Kernel.mul_disequality,OpenNetworkComposition.spliceTensor,binarySignature,
    Signature.disequality,mul_comm]

theorem realizes_onePort {n : ℕ} (F : SignatureFamily ℂ) (f : Signature ℂ (n+1)) (B : Mat)
    (hf : Gadget.Realizes F .disequality f) (hB : Gadget.Realizes F .disequality (binarySignature B)) :
    Gadget.Realizes F .disequality (onePort f (transfer B) 0) := by
  rw [onePort_eq_splice]
  exact OpenNetworkComposition.realizes_splice F _ _ hf hB 0

theorem det_transfer (B : Mat) : det (transfer B)= -det B := by
  simp [det,transfer,Kernel.mul_disequality]

def ActualSafeBinary (F : SignatureFamily ℂ) (B : Mat) : Prop :=
  Gadget.Realizes F .disequality (binarySignature B) ∧ det B≠0 ∧
    Certificates.TwelveLoops.ProjectivelyFinite (Matrix.of (transfer B))
def safeFamily (F : SignatureFamily ℂ) (B : {B : Mat // ActualSafeBinary F B}) : Mat := B.val

theorem safe_native_X (F : SignatureFamily ℂ) : ActualSafeBinary F Signature.disequality := by
  refine ⟨Gadget.realizes_edgeBox F .disequality,?_,?_⟩
  · norm_num [det,Signature.disequality]
  · refine ⟨1,by decide,1,one_ne_zero,?_⟩
    simp [transfer,Kernel.disequality_mul_disequality]
    rfl

theorem safe_literal_I (F : SignatureFamily ℂ)
    (hI : (⟨2,binarySignature Signature.equality⟩ : AnySignature ℂ)∈F) :
    ActualSafeBinary F Signature.equality := by
  refine ⟨Gadget.realizes_of_mem F .disequality _ hI,?_,?_⟩
  · norm_num [det,Signature.equality]
  · refine ⟨2,by decide,1,one_ne_zero,?_⟩
    simp only [transfer,Kernel.equality_mul,one_smul,pow_two]
    ext a b
    cases a <;> cases b <;> simp [Matrix.mul_apply,Matrix.one_apply,Signature.disequality]

@[simp] theorem onePort_identity {n : ℕ} (q : Signature ℂ n) (p : Fin n) :
    onePort q Signature.equality p=q := by
  simp [onePort,Signature.coordinateAction_equality]

theorem base_deck_of_safe_dressings (F : SignatureFamily ℂ) (q : Signature ℂ 8)
    (hd : ∀ B,ActualSafeBinary F B → PhysicalDeck (onePort q (transfer B) 0)) : PhysicalDeck q := by
  have h := hd Signature.disequality (safe_native_X F)
  simpa [transfer] using h

theorem proper_safe_transfer (F : SignatureFamily ℂ)
    (hspan : Observability.linkedChainSpan (safeFamily F)=Observability.ixSpan)
    (B : Mat) (hB : ActualSafeBinary F B) : transfer B∈Observability.ixSpan := by
  rw [Observability.linkedChainSpan_eq] at hspan
  have hm := (Observability.chainSpan_eq_ixSpan_iff _).mp hspan ⟨B,hB⟩
  exact Observability.ixSpan_mul_mem _ hm _ Observability.disequality_mem_ixSpan

end
end Holant.ReedMuller.SafeCollapse
