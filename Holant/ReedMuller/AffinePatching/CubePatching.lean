import Holant.ReedMuller.AffinePatching.SupportPatching

/-! Every actual third-difference cube fits in an accessible annihilating
hyperplane. This transfers the local phase identity with all cancellation
and repeated-direction cases intact. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 theorem binaryDot_xor_left (x y v : Word n) :
    binaryDot (AffinePhase.xor x y) v=binaryDot x v+binaryDot y v := by
  simp only [binaryDot_vector,vector_xor,dot_add_left]

 theorem global_supported_cube (hn : 7≤n) (F : Signature AlgebraicComplex n)
    (hF : HyperplaneAffine F) (z u v w : Word n)
    (hs : ∀ i,F (cubeWords z u v w i)≠0) : thirdRatio F z u v w=1 := by
  obtain ⟨p,hp,hd⟩ := exists_accessible_orthogonal (k:=4) hn
    ![vectorWord z,vectorWord u,vectorWord v,vectorWord w]
  have hz : binaryDot z (wordVector p)=0 := by
    rw [binaryDot_vector,vector_word,dot_comm]
    exact hd 0
  have hu : binaryDot u (wordVector p)=0 := by
    rw [binaryDot_vector,vector_word,dot_comm]
    exact hd 1
  have hv : binaryDot v (wordVector p)=0 := by
    rw [binaryDot_vector,vector_word,dot_comm]
    exact hd 2
  have hw : binaryDot w (wordVector p)=0 := by
    rw [binaryDot_vector,vector_word,dot_comm]
    exact hd 3
  have hc : ∀ i,binaryDot (cubeWords z u v w i) (wordVector p)=0 := by
    intro i
    fin_cases i <;> simp [cubeWords,binaryDot_xor_left,hz,hu,hv,hw]
  have he : ∀ i,hyperplaneMask (wordVector p) F (cubeWords z u v w i)=F (cubeWords z u v w i) := by
    intro i
    exact if_pos (hc i)
  have hm : ∀ i,hyperplaneMask (wordVector p) F (cubeWords z u v w i)≠0 := by
    intro i;rw [he];exact hs i
  have H := affine_supported_cube _ (hF p hp) z u v w hm
  change (hyperplaneMask (wordVector p) F (cubeWords z u v w 7)*
    hyperplaneMask (wordVector p) F (cubeWords z u v w 1)*
    hyperplaneMask (wordVector p) F (cubeWords z u v w 2)*
    hyperplaneMask (wordVector p) F (cubeWords z u v w 3))/
    (hyperplaneMask (wordVector p) F (cubeWords z u v w 4)*
    hyperplaneMask (wordVector p) F (cubeWords z u v w 5)*
    hyperplaneMask (wordVector p) F (cubeWords z u v w 6)*
    hyperplaneMask (wordVector p) F (cubeWords z u v w 0))=1 at H
  simp only [he] at H
  exact H

end
end Holant.ReedMuller.AffinePatching
