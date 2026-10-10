import Holant.Certificates.AffineEndpoint.CoreData

namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def coreMatrix (k : CoreIndex) : Matrix Bool Bool AlgebraicComplex := algebraicMatrix (coreRaw k)
 def algMat (a b c d : AlgebraicComplex) : Matrix Bool Bool AlgebraicComplex :=
  fun x y => if x then if y then d else c else if y then b else a

 theorem core_identity : coreMatrix (.inl 0)=(1 : Matrix Bool Bool AlgebraicComplex) := by
  ext a b
  cases a <;> cases b <;> simp [coreMatrix,coreRaw,algebraicMatrix,q,mat,Matrix.one_apply]

 theorem core_flip : coreMatrix (.inl 1)=(fun a b => Signature.disequality a b) := by
  ext a b
  cases a <;> cases b <;> simp [coreMatrix,coreRaw,algebraicMatrix,OctahedralSeparator.flip,mat,Signature.disequality]

 theorem core_hadamard (k : Fin 8) : coreMatrix (.inr (.inl k))=
    algMat 1 (zetaEight^k.val) 1 (-(zetaEight^k.val)) := by
  ext a b
  cases a <;> cases b <;> simp [coreMatrix,coreRaw,algebraicMatrix,mat,algMat]

 theorem core_mixed (k : Fin 4) (b : Bool) : coreMatrix (.inr (.inr (k,b)))=
    let s : AlgebraicComplex := if b then -sqrtTwo else sqrtTwo
    algMat 1 (imaginaryUnit^k.val*(1+s)) 1 (imaginaryUnit^k.val*(1-s)) := by
  cases b <;> ext a b <;> cases a <;> cases b <;>
    simp [coreMatrix,coreRaw,algebraicMatrix,mat,algMat]

 theorem coreMatrix_injective : Function.Injective coreMatrix :=
  fun _ _ h => coreRaw_injective (algebraicMatrix_injective h)

 theorem algebraicMatrix_determinant (U : Mat) :
    (algebraicMatrix U).det=algebraicEmbed (determinant U) := by
  have h := Matrix.det_reindex_self binaryFinEquiv (algebraicMatrix U)
  rw [Matrix.det_fin_two] at h
  simpa [determinant,algebraicMatrix,Matrix.reindex_apply,binaryFinEquiv] using h.symm

 theorem coreMatrix_nonsingular (k : CoreIndex) : (coreMatrix k).det≠0 := by
  rw [coreMatrix,algebraicMatrix_determinant]
  exact algebraicEmbed_ne_zero (coreRaw_nonsingular k)

 def coreSet : Finset (Matrix Bool Bool AlgebraicComplex) :=
  Finset.univ.map ⟨coreMatrix,coreMatrix_injective⟩

 theorem coreSet_card : coreSet.card=18 := by
  simp [coreSet,core_index_card]

end
end Holant.Certificates.AffineEndpoint
