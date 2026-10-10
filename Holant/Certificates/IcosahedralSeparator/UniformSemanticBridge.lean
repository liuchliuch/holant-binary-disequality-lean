import Holant.Certificates.IcosahedralSeparator.UniformPredicates

/-! Soundness of the finite rank and projective rejection certificates in
the original complex matrices and port coordinates. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

 theorem uniform_rank_three_of_check (i : Fin 30) (hc : UniformRankCheck i) (k : Fin 3) :
    Matrix.rank (flatten k (uniformOutput i))=3 := by
  let M : PairMatrix:=fun a b=>gembed (flatCode i k a b)
  have hd : Matrix.det M=0 := by
    have hh:=congrArg gembed (hc k).1
    rw [gembed_gdet4,gembed_zero] at hh
    have hh' : Matrix.det (M.submatrix pairEquiv pairEquiv)=0 := hh
    simpa using hh'
  have hm : Matrix.det (M.submatrix
      (fun a=>pairIndex (uniformRankRows i k a))
      (fun b=>pairIndex (uniformRankCols i k b)))≠0 := by
    have hh:=gembed_ne_zero (hc k).2
    rwa [gembed_gdet3] at hh
  have hr:=rank_three_of_minor M _ _ hd hm
  have he : M=(8:ℂ) • flatten k (uniformOutput i) := by
    ext a b
    exact gembed_flatCode i k a b
  rw [he,Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero (by norm_num : (8:ℂ)≠0))] at hr
  exact hr

 theorem subsequent_nonsingular_of_check (i : Fin 30) (hc : UniformOutsideCheck i) :
    Matrix.det (Matrix.of (subsequentOutput i))≠0 := by
  intro hz
  apply gembed_ne_zero hc.1
  have he : gembed (binaryDetCode i)=64*binaryDeterminant (subsequentOutput i) := by
    simp [binaryDetCode,gembed_binaryCode,binaryDeterminant]
    ring
  rw [he,binaryDeterminant_eq_det,hz,mul_zero]

 theorem subsequent_transfer_outside_of_check (i : Fin 30) (hc : UniformOutsideCheck i) :
    ¬groupDirection .icosahedral (Kernel.mul (subsequentOutput i) Signature.disequality) := by
  intro h
  obtain ⟨j,c,hc0,he⟩:=(complete .icosahedral _).mp h
  let a:=pairIndex (outsideFirst i j)
  let b:=pairIndex (outsideSecond i j)
  have hn:=gembed_ne_zero (hc.2 j)
  apply hn
  simp only [gembed_sub,gembed_mul,gembed_transferCode,gembed_groupCode]
  have hv (u v : Bool) : Kernel.mul (subsequentOutput i) Signature.disequality u v=
      c*representative .icosahedral j u v := by
    simpa only [Matrix.smul_apply,smul_eq_mul] using
      congrArg (fun M : Matrix Bool Bool ℂ=>M u v) he
  have ha:=hv a.1 a.2
  have hb:=hv b.1 b.2
  change (8*Kernel.mul (subsequentOutput i) Signature.disequality a.1 a.2)*representative .icosahedral j b.1 b.2-
    (8*Kernel.mul (subsequentOutput i) Signature.disequality b.1 b.2)*representative .icosahedral j a.1 a.2=0
  rw [ha,hb]
  ring

 theorem uniformKernel_representative : uniformKernel=representative .icosahedral (21 : Fin 60) := by
  funext a b
  cases a <;> cases b <;>
    simp [uniformKernel,representative,raw,goldenMatrix,quaternion,quaternionBasis,
      icosahedralRaw,GoldenInt.eval,GoldenInt.reciprocal_eq,Q0,Q1,Q2,Q3,Signature.equality,Fin.sum_univ_succ] <;>
    push_cast <;> ring

 theorem subsequentKernel_representative :
    subsequentKernel=(goldenReciprocal : ℂ) • representative .icosahedral (45 : Fin 60) := by
  funext a b
  cases a <;> cases b <;>
    simp [subsequentKernel,representative,raw,goldenMatrix,quaternion,quaternionBasis,
      icosahedralRaw,GoldenInt.eval,GoldenInt.reciprocal_eq,Q0,Q1,Q2,Q3,Signature.equality,Fin.sum_univ_succ]
  all_goals push_cast
  all_goals have h : (goldenRatio : ℂ)^2=goldenRatio+1 := by exact_mod_cast GoldenInt.golden_sq
  all_goals ring_nf
  all_goals try rw [h]
  all_goals ring

 theorem uniformKernel_group : groupDirection .icosahedral uniformKernel := by
  rw [uniformKernel_representative]
  exact representative_mem .icosahedral (21 : Fin 60)

 theorem subsequentKernel_group : groupDirection .icosahedral subsequentKernel := by
  apply (complete .icosahedral _).mpr
  refine ⟨(45 : Fin 60),(goldenReciprocal : ℂ),?_,subsequentKernel_representative⟩
  exact_mod_cast (show goldenReciprocal≠0 by exact inv_ne_zero GoldenInt.golden_ne_zero)

end
end Holant.Certificates.IcosahedralSeparator
