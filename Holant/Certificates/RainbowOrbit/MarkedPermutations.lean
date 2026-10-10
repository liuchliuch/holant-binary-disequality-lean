import Holant.Certificates.RainbowOrbit.MarkedFamily
import Holant.Certificates.RainbowOrbit.PortPermutations
import Holant.Certificates.OctahedralSeparator.TensorTransport

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

def permutationCorrection (f : Form) (e : Equiv.Perm (Fin 4)) : Legs :=
  fun j => markLegs f j*(markLegs f (e.symm j))⁻¹

theorem marked_permutation_intertwine (f : Form) (e : Equiv.Perm (Fin 4)) (F : FourTensor) :
    act (permutationCorrection f e) (Tensor.reindex e (act (markLegs f) F))=
      act (markLegs f) (Tensor.reindex e F) := by
  change Signature.coordinateAction _ (Tensor.reindex e (Signature.coordinateAction _ F))=_
  rw [reindex_action]
  change act _ (act _ (Tensor.reindex e F))=_
  rw [act_comp]
  congr 1
  funext j
  simp only [permutationCorrection,mul_assoc,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (markLegs_det f (e.symm j))),mul_one]

theorem theta_markS (f : Form) : complexTheta f (markS f)=(markH f).transpose*markH f := by
  change (markH f)⁻¹*((markH f*(markH f).transpose)*markH f)=_
  rw [←mul_assoc,←mul_assoc,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (markH_det f)),one_mul]

theorem theta_markSinv (f : Form) : complexTheta f (markSinv f)=(markH f)⁻¹*(markH f)⁻¹.transpose := by
  change (markH f)⁻¹*(((markH f)⁻¹.transpose*(markH f)⁻¹)*markH f)=_
  rw [mul_assoc (markH f)⁻¹.transpose,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (markH_det f)),mul_one]

/-- The only corrections introduced by adjacent swaps are I, θ(S), θ(S⁻¹),
all actual current-group directions. Their ordered positions are explicit. -/
theorem adjacent_correction_exact (f : Form) (j : Fin 3) :
    permutationCorrection f (adjacent j)=
      (![![complexTheta f (markSinv f),complexTheta f (markS f),1,1],
          ![1,complexTheta f (markS f),complexTheta f (markSinv f),1],
          ![1,1,complexTheta f (markSinv f),complexTheta f (markS f)]] : Fin 3→Legs) j := by
  have hi := isUnit_iff_ne_zero.mpr (markH_det f)
  have ht : (markH f).transpose.det≠0 := by simpa using markH_det f
  funext q
  fin_cases j <;> fin_cases q <;>
    simp [permutationCorrection,adjacent,markLegs_eq,Equiv.swap_apply_def,theta_markS,theta_markSinv,
      Matrix.transpose_nonsing_inv,Matrix.nonsing_inv_nonsing_inv _ hi,
      Matrix.nonsing_inv_mul _ hi,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht)]

theorem adjacent_correction_mem (f : Form) (j : Fin 3) :
    ∀q,Direction f (permutationCorrection f (adjacent j) q) := by
  have hs : Direction f (complexTheta f (markS f)) :=
    (direction_iff_source_conjugate f _).mpr ⟨_,markS_source f,rfl⟩
  have ht : Direction f (complexTheta f (markSinv f)) :=
    (direction_iff_source_conjugate f _).mpr ⟨_,markSinv_source f,rfl⟩
  intro q
  rw [adjacent_correction_exact]
  fin_cases j <;> fin_cases q <;>
    first | exact hs | exact ht | exact (markedMatrixFamily f).one

/-- The transported adjacent swap is the same physical port swap followed by
four actual current-group representatives. No coefficient similarity is a resource. -/
theorem adjacent_correction_physical (f : Form) (j : Fin 3) (F : FourTensor) :
    ∃k : Fin 4→Fin 24,∃c : Fin 4→ℂ,(∀q,c q≠0) ∧
      (physicalNetwork (Tensor.reindex (adjacent j) (act (markLegs f) F))
        (fun q => complexMatrix (theta f (standard (k q))))).denote=
          (∏q,c q)⁻¹ • act (markLegs f) (Tensor.reindex (adjacent j) F) := by
  have hm := adjacent_correction_mem f j
  choose c hc k hk using hm
  refine ⟨k,c,hc,?_⟩
  have he : permutationCorrection f (adjacent j)=
      (fun q => c q • complexMatrix (theta f (standard (k q)))) := funext hk
  have hh := marked_permutation_intertwine f (adjacent j) F
  rw [he,act_rescale_legs] at hh
  have hn : (∏q,c q)≠0 := Finset.prod_ne_zero_iff.mpr (fun q _ => hc q)
  rw [physicalNetwork_denote_act,←hh,smul_smul,inv_mul_cancel₀ hn,one_smul]

end
end Holant.Certificates.RainbowOrbit
