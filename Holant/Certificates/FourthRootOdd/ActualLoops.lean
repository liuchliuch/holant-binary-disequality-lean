import Holant.Certificates.FourthRootOdd.SeriesEquality
import Holant.Certificates.FourthRootOdd.TwoCopy
import Holant.Certificates.TwelveLoops.Source

/-! The A.1 exits as actual same-resource binary gadgets, including the
equality-mediated loops and the native-loop series-I support flip. -/
noncomputable section
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops

abbrev LoopIndex := Bool × Fin 6
def coefficients (s : State) (i : LoopIndex) : Gaussian × Gaussian :=
  if i.1 then equalityPair s i.2 else nativePair s i.2
def loopOutput (f : Signature ℂ 4) (i : LoopIndex) : Signature ℂ 2 :=
  if i.1 then equalityContract f i.2 else flipSecond (nativeContract f i.2)
def signatureMatrix (f : Signature ℂ 2) : Matrix Bool Bool ℂ := fun a b => f ![a,b]

theorem coefficients_complete (s : State) (p : Gaussian × Gaussian) (hp : p∈loopPairs s) :
    ∃ i : LoopIndex,coefficients s i=p := by
  simp only [loopPairs,List.mem_append,List.mem_ofFn] at hp
  rcases hp with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact ⟨(false,i),rfl⟩
  · exact ⟨(true,i),rfl⟩

theorem loopOutput_realizes (f : Signature ℂ 4) (i : LoopIndex) :
    Gadget.Realizes (loopResources f) .disequality (loopOutput f i) := by
  rcases i with ⟨k,p⟩
  cases k
  · exact flipped_nativeContract_realizes f p
  · exact equalityContract_realizes f p

theorem loopOutput_matrix (s : State) (i : LoopIndex) :
    signatureMatrix (loopOutput (complexOdd s) i)=offMatrix (coefficients s i).1 (coefficients s i).2 := by
  rcases i with ⟨k,p⟩
  cases k
  · ext a b
    exact congrFun (congrFun (native_loop_matrix s p) a) (!b)
  · have h := equality_loop_matrix s p
    change (fun x y : Bool => loopAt (fun j => embed (a s j)) (fun j => embed (b s j)) p false ![x,y]) =
      offMatrix (equalityPair s p).1 (equalityPair s p).2
    simpa only [equality_mediated_eq] using h

theorem loopOutput_transfer (s : State) (i : LoopIndex) :
    signatureMatrix (loopOutput (complexOdd s) i)*TwelveLoops.flip=transfer (coefficients s i).1 (coefficients s i).2 := by
  rw [loopOutput_matrix,off_mul_flip]

theorem transfer_isUnit (P Q : Gaussian) (hP : P≠(0,0)) (hQ : Q≠(0,0)) : IsUnit (transfer P Q) := by
  have hp : embed P≠0 := (not_congr (embed_zero_iff _)).mpr hP
  have hq : embed Q≠0 := (not_congr (embed_zero_iff _)).mpr hQ
  let V : Matrix Bool Bool ℂ := Matrix.diagonal (fun j => if j then (embed Q)⁻¹ else (embed P)⁻¹)
  refine ⟨{val:=transfer P Q,inv:=V,val_inv:=?_,inv_val:=?_},rfl⟩
  all_goals ext a b; cases a <;> cases b <;> simp [transfer,V,Matrix.mul_apply,hp,hq]

theorem actual_rankOne_route (s : State) (hs : classify s=.rankOne) :
    ∃ i : LoopIndex, (signatureMatrix (loopOutput (complexOdd s) i)).rank=1 ∧
      Gadget.Realizes (loopResources (complexOdd s)) .disequality (loopOutput (complexOdd s) i) := by
  obtain ⟨p,hp,_,hr⟩ := rankOne_exit s hs
  obtain ⟨i,hi⟩ := coefficients_complete s p hp
  refine ⟨i,?_,loopOutput_realizes _ _⟩
  rw [loopOutput_matrix,hi]
  exact hr

theorem actual_infinite_route (s : State) (hs : classify s=.infiniteOrder) :
    ∃ i : LoopIndex, Gadget.Realizes (loopResources (complexOdd s)) .disequality (loopOutput (complexOdd s) i) ∧
      IsUnit (signatureMatrix (loopOutput (complexOdd s) i)*TwelveLoops.flip) ∧
      ¬ProjectivelyFinite (signatureMatrix (loopOutput (complexOdd s) i)*TwelveLoops.flip) := by
  obtain ⟨p,hp,hP,hQ,hi⟩ := infiniteOrder_exit s hs
  obtain ⟨i,he⟩ := coefficients_complete s p hp
  refine ⟨i,loopOutput_realizes _ _,?_⟩
  rw [loopOutput_transfer,he]
  exact ⟨transfer_isUnit p.1 p.2 hP hQ,hi⟩

end Holant.Certificates.FourthRootOdd
