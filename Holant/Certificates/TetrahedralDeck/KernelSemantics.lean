import Holant.Certificates.TetrahedralDeck.FiniteData
import Holant.Certificates.TwelveLoops.Gaussian
import Holant.Certificates.TetrahedralAffine.Semantics
import Holant.Certificates.TetrahedralAffine.Binaries

/-! Exact interpretation of the finite Gaussian kernel family in the literal
complex tetrahedral model. No projective scalars are discarded. -/
namespace Holant.Certificates.TetrahedralDeck
open Holant Holant.Certificates.TwelveLoops Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def representative (k : Fin 12) : TetrahedralAffine.Representative :=
  Fin.addCases (motive := fun _ : Fin 12 => TetrahedralAffine.Representative)
    Sum.inl (fun j => Sum.inr (signs j)) k

def actualKernel (k : Fin 12) : Binary := TetrahedralAffine.complexKernel (representative k)

theorem representative_surjective : Function.Surjective representative := by
  intro r
  cases r with
  | inl k => exact ⟨k.castAdd 8,by simp [representative]⟩
  | inr ε =>
    obtain ⟨j,rfl⟩ := signs_surjective ε
    exact ⟨j.natAdd 4,by simp [representative]⟩

theorem embed_gneg (z : Gaussian) : embed (gneg z) = -embed z := by simp [embed,gneg]; ring

theorem embed_gQ (k : Fin 4) (a b : Bool) : embed (gQ k a b) = quaternionBasis k a b := by
  fin_cases k <;> cases a <;> cases b <;>
    norm_num [gQ,gzero,gone,gI,embed,quaternionBasis,Q0,Q1,Q2,Q3,Signature.equality]

theorem embed_gKernel (k : Fin 12) (a b : Bool) : embed (gKernel k a b) = actualKernel k a b := by
  refine Fin.addCases (m := 4) (n := 8) (fun i => ?_) (fun j => ?_) k
  · simpa [gKernel,actualKernel,representative,TetrahedralAffine.complexKernel] using embed_gQ i a b
  · simp only [gKernel,actualKernel,representative,Fin.addCases_right,TetrahedralAffine.complexKernel]
    fin_cases j <;> cases a <;> cases b <;>
      norm_num [quaternion,quaternionBasis,signs,signBit,gSigned,gneg,gadd,gQ,gzero,gone,gI,
        Q0,Q1,Q2,Q3,Signature.equality,embed] <;> ring

theorem kernel_direction (k : Fin 12) : groupDirection .tetrahedral (actualKernel k) :=
  ⟨1,one_ne_zero,_,TetrahedralAffine.kernel_base (representative k),by simp [actualKernel]⟩

theorem kernel_actual (k : Fin 12) : groupDirection .tetrahedral (multiply (actualKernel k) X) :=
  groupDirection_right_X _ (kernel_direction k)

theorem kernel_nonsingular (k : Fin 12) : Matrix.det (Matrix.of (actualKernel k)) ≠ 0 :=
  groupDirection_det_ne_zero _ (kernel_direction k)

end
end Holant.Certificates.TetrahedralDeck
