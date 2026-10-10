import Holant.ReedMuller.SupportReconstruction.SliceWeight
import Holant.ReedMuller.RadonAccess.Directions

/-! Literal form of equation rm-local-code: the residual matching word plus
the parity of its logical weight on both original deleted coordinates. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant.ReedMuller.LowArity Holant.ReedMuller.ZeroCardGraph
open Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
open scoped BigOperators
variable {n r : ℕ} {i j : Fin n}

 def matchingWord (p : (Fin r × Bool) ≃ Remaining i j) (t : BinaryVector r) : BinaryVector n :=
   fun k=>if hi : k=i then 0 else if hj : k=j then 0 else t (p.symm ⟨k,hi,hj⟩).1

 theorem matchingWord_left (p : (Fin r × Bool) ≃ Remaining i j) (t : BinaryVector r) :
     matchingWord p t i=0 := by simp [matchingWord]
 theorem matchingWord_right (p : (Fin r × Bool) ≃ Remaining i j) (t : BinaryVector r) :
     matchingWord p t j=0 := by by_cases h : j=i <;> simp [matchingWord,h]
 theorem matchingWord_port (p : (Fin r × Bool) ≃ Remaining i j) (t : BinaryVector r) (e : Fin r) (b : Bool) :
     matchingWord p t (p (e,b)).val=t e := by
   simp [matchingWord,(p (e,b)).property.1,(p (e,b)).property.2]

 theorem sliceWord_decomposition (p : (Fin r × Bool) ≃ Remaining i j) (hij : i≠j) (t : BinaryVector r) :
     sliceWord p t=matchingWord p t+(binaryWeight t:ZMod 2) • (unitWord i+unitWord j) := by
   have hpar : (∑e,t e)=(binaryWeight t:ZMod 2) := by rw [cast_binaryWeight,dot_self]
   funext k
   by_cases hi : k=i
   · subst k
     simp [sliceWord,matchingWord,unitWord_apply,hij,hpar]
   · by_cases hj : k=j
     · subst k
       simp [sliceWord,matchingWord,unitWord_apply,hi,hpar]
     · simp [sliceWord,matchingWord,unitWord_apply,hi,hj]

 theorem mem_slice_formula (p : (Fin r × Bool) ≃ Remaining i j) (hij : i≠j) (x : BinaryVector n) :
     x∈sliceCode p ↔ ∃t : BinaryVector r,
       x=matchingWord p t+(binaryWeight t:ZMod 2) • (unitWord i+unitWord j) := by
   rw [mem_sliceCode]
   simp only [sliceWord_decomposition p hij,eq_comm]

end Holant.ReedMuller.SupportReconstruction
