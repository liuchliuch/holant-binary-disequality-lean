import Holant.Certificates.PlatonicDeficient.OutputData
import Holant.Certificates.OctahedralSeparator.BaseRanks
import Holant.Certificates.OctahedralSeparator.PhysicalOutputs
import Holant.Certificates.OctahedralSeparator.CardMap
import Holant.Certificates.IcosahedralSeparator.UniformRankThree
import Holant.Certificates.MatchingProductBridge.Exceptionals

/-! A.24 reconstruction, exact original-port contractions, and complex ranks.
The O′ tensor is obtained by actual current-group correction legs after an I
contraction. Its uniform H⁻¹ formula is only an analytic equality. -/
namespace Holant.Certificates.PlatonicDeficient
open Holant Holant.Certificates.OctahedralSeparator
open Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev output := PlatonicQuaternaryExits.Deficient.output
abbrev primeOutput := PlatonicQuaternaryExits.Deficient.primeOutput

def ancestor (p : Fin 6) : Signature ℂ 6 := complexTensor (reconstruct (deficientImages p))
def primeAncestor (p : Fin 6) : Signature ℂ 6 := complexTensor (deficientAncestor 1 p)
def support (t : Signature ℂ 4) : Finset (Fin 4 → Bool) := by
  classical
  exact Finset.univ.filter (fun x => t x ≠ 0)

theorem common_coefficient_tuple (p : Fin 6) :
    deficientImages p = Fin.cons (tensorScale (rat (1/2)) cTensor)
      (fun j => ![0,tensorScale (rat (1/2)) aTensor,tensorScale (rat (1/2)) bTensor]
        (permutations p j)) := rfl

theorem reconstructed_basis_cards (p : Fin 6) (μ : Fin 4) :
    Signature.contract (complexMatrix (q μ)) (ancestor p) =
      complexTensor (deficientImages p μ) := by
  rw [ancestor,←complexTensor_contract,quaternion_card_reconstruct]

theorem output_contract (p : Fin 6) :
    output p = Signature.contract Q0
      (Tensor.reindex (TetrahedralDeck.portOrder 1).symm (ancestor p)) := by
  change complexTensor (deficientCard p) = _
  rw [deficientCard,complexTensor_contract,complexTensor_reindex,complexMatrix_q]
  rfl

/-- The original standard-form six-port tensor and actual current-group binary
vertices. This definition is uniform in the three standard T/O/I models. -/
def standardResources (g : PlatonicModel) (h : Signature ℂ 6) : SignatureFamily ℂ :=
  {s | s = ⟨6,h⟩ ∨ ∃ U : Native.Binary,
    s = ⟨2,Native.binarySignature U⟩ ∧ groupDirection g (nativeTransfer U)}

theorem standard_pair_available (g : PlatonicModel) :
    groupDirection g (nativeTransfer (Native.pairVertex Q0)) := by
  have he : nativeTransfer (Native.pairVertex Q0) = X := by
    ext a b
    cases a <;> cases b <;>
      simp [nativeTransfer,Native.pairVertex,Kernel.mul,Q0,X,
        Signature.equality,Signature.disequality]
  rw [he]
  exact X_direction g

theorem standard_identity_leg_available (g : PlatonicModel) :
    groupDirection g (nativeTransfer (Native.legVertex Signature.equality)) := by
  have he : nativeTransfer (Native.legVertex Signature.equality) = Q0 := by
    ext a b
    simp [nativeTransfer,Native.legVertex,Q0]
  rw [he]
  exact quaternion_axis_direction g 0

/-- Actual I contraction with native X edges and only permitted standard-form
binaries. The four boundary legs are identities. -/
theorem output_realizes (g : PlatonicModel) (p : Fin 6) :
    Gadget.Realizes (standardResources g (ancestor p)) .disequality (output p) := by
  rw [output_contract]
  have hh := Native.ordered_dressed_realizes_of_mem
    (standardResources g (ancestor p)) (TetrahedralDeck.portOrder 1).symm
    (ancestor p) Q0 (fun _ => Signature.equality)
    (Or.inl rfl)
    (Or.inr ⟨_,rfl,standard_pair_available g⟩)
    (fun _ => Or.inr ⟨_,rfl,standard_identity_leg_available g⟩)
  simpa only [Signature.coordinateAction_equality] using hh

theorem output_support_ten (p : Fin 6) : (support (output p)).card = 10 := by
  classical
  have he : support (output p) = scalarSupport p := by
    ext x
    simp only [support,scalarSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    change embed (deficientCard p x) ≠ 0 ↔ cachedBase (p.natAdd 9) x ≠ 0
    rw [PlatonicQuaternaryExits.Deficient.cached_deficient]
    exact not_congr (by rw [←embed_zero]; exact embed_injective.eq_iff)
  rw [he,scalar_support_ten]

theorem output_rank_three (p : Fin 6) (r : Fin 3) :
    (flatten r (output p)).rank = 3 := by
  let M := scalarFlatten r (cachedBase (p.natAdd 9))
  have he : (fun a b => embed (M a b)) = flatten r (output p) := by
    rw [scalarFlatten_embed,PlatonicQuaternaryExits.Deficient.cached_deficient]
    rfl
  apply IcosahedralSeparator.rank_three_of_minor _ minorStates minorStates
  · have hh := congrArg embed (deficient_determinant_zero p r)
    rw [show embed (Matrix.det M) = Matrix.det (fun a b => embed (M a b)) from
      embedding.map_det M,embed_zero,he] at hh
    exact hh
  · have hh := embed_ne_zero (deficient_minor_nonzero p r)
    rw [show embed (Matrix.det (M.submatrix minorStates minorStates)) =
      Matrix.det (fun a b => embed (M (minorStates a) (minorStates b))) from
      embedding.map_det (M.submatrix minorStates minorStates)] at hh
    change Matrix.det ((show Matrix PairIndex PairIndex ℂ from fun a b => embed (M a b)).submatrix minorStates minorStates) ≠ 0 at hh
    rwa [he] at hh

theorem primeOutput_eq_corrected (p : Fin 6) :
    primeOutput p = complexTensor (correctedCard 1 (p.natAdd 9)) := by
  change complexTensor (Signature.coordinateAction (fun _ => inverseConjugator 1)
    (cachedBase (p.natAdd 9))) = _
  rw [PlatonicQuaternaryExits.Deficient.cached_deficient]
  simp only [correctedCard,baseCard,Fin.addCases_right]

/-- Literal analytic transport identity, with no gadget assertion for H⁻¹. -/
theorem primeOutput_transport (p : Fin 6) :
    primeOutput p = Signature.coordinateAction
      (fun _ => complexMatrix (inverseConjugator 1)) (output p) := by
  rw [primeOutput_eq_corrected,correctedCard,complexTensor_action]
  simp only [baseCard,Fin.addCases_right]
  rfl

/-- Actual O′ contraction and current-group leg dressings in original coordinates. -/
theorem primeOutput_actual (p : Fin 6) :
    primeOutput p = Signature.coordinateAction
      (fun j => complexMatrix (corrections 1 j))
      (Signature.contract Q0
        (Tensor.reindex (TetrahedralDeck.portOrder 1).symm (primeAncestor p))) := by
  rw [primeOutput_eq_corrected,←corrections_exact,complexTensor_action]
  congr 1
  rw [primeAncestor,←complexTensor_reindex]
  have h0 : Q0 = complexMatrix (q 0) := (complexMatrix_q 0).symm
  rw [h0,←complexTensor_contract,deficient_card_exact]

theorem prime_kernel_available : Direction 1 (Matrix.of Q0) := by
  simpa [complexMatrix_q,quaternionBasis] using direction_identity 1

theorem prime_legs_available (j : Fin 4) :
    Direction 1 (complexMatrix (corrections 1 j)) := corrections_available 1 j

/-- The graph uses the actual O′ ancestor, an I pair kernel, and four actual
O′ legs. This proves provenance independently of the analytic H formula. -/
theorem primeOutput_realizes (p : Fin 6) :
    Gadget.Realizes (markedResources 1 (primeAncestor p)) .disequality (primeOutput p) := by
  rw [primeOutput_actual]
  apply Native.ordered_dressed_realizes_of_mem
  · exact markedResources_ancestor _ _
  · exact markedResources_binary _ _ _ (pairVertex_available prime_kernel_available)
  · intro j
    exact markedResources_binary _ _ _ (legVertex_available (prime_legs_available j))

theorem primeOutput_rank_three (p : Fin 6) (r : Fin 3) :
    (flatten r (primeOutput p)).rank = 3 := by
  rw [primeOutput_transport,flatten_rank_coordinateAction]
  · exact output_rank_three p r
  · intro j
    rw [complexMatrix_inverseConjugator,Matrix.det_nonsing_inv]
    simpa using inv_ne_zero (complexMatrix_conjugator_det_ne_zero 1)

end
end Holant.Certificates.PlatonicDeficient
