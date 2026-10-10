import Holant.Certificates.OppositeIcosahedral.FixedNative
import Holant.Certificates.OppositeIcosahedral.NativeEdgeScalars

/-! Complete fixed-equality coefficient dictionary of source Lemma9.2,
paper1.tex12777–12834. The opposite group is the literal odd-permutation golden
display, not an assumed conjugate family. The native realization leaves every
original signature occurrence and its ordered boundary ports unchanged. -/
namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section

/-- The actual displayed group and the actual kernel classes are identified
separately: conjugation for the former, κ for the latter. -/
theorem fixed_equality_kernel_dictionary :
    (∀U : Mat,Direction U ↔ ∃V : Mat,groupDirection .icosahedral V ∧ U=conjugate V) ∧
    (∀K : Mat,Direction (kappa K) ↔ groupDirection .icosahedral K) ∧
    Function.Bijective kernelIndex ∧
    (∀i : Fin 60,kernelScale i≠0 ∧
      kappa (standardRepresentative i)=kernelScale i • oppositeRepresentative (kernelIndex i)) :=
  ⟨direction_iff_conjugate,kernel_membership_iff,kernelIndex_bijective,
    fun i => ⟨kernelScale_ne_zero i,kernel_representative_exact i⟩⟩

/-- Original ordered-pair covariance and the complete zero/support clauses. -/
theorem fixed_equality_card_dictionary {n : ℕ} (p : Equiv.Perm (Fin (n+2)))
    (f : Signature ℂ (n+2)) (K : Mat) :
    card p f (kappa K)=transport (card p (analytical f) K) ∧
    (card p f (kappa K)=0 ↔ card p (analytical f) K=0) ∧
    (∀x,card p f (kappa K) x≠0 ↔ card p (analytical f) K x≠0) :=
  ⟨card_covariance p f K,zero_card_iff p f K,card_support_preserved p f K⟩

/-- A finite identity on the analytical tuple produces an actual native-X
network identity on the original resources with all nonzero scalars recorded. -/
theorem fixed_equality_network_dictionary {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) :
    realizationScale i≠0 ∧
    (fixedNativeNetwork s f i).denote=realizationScale i •
      transport (analyticalNetwork s f (fun e => standardRepresentative (i e))).denote ∧
    Gadget.Realizes (fixedResources s f) .disequality (realizationScale i •
      transport (analyticalNetwork s f (fun e => standardRepresentative (i e))).denote) ∧
    (∀v,fixedNativeLabels s f i (.inl v)=f v) :=
  ⟨realizationScale_ne_zero i,fixedNativeNetwork_denote s f i,fixedNativeNetwork_realizes s f i,
    original_vertex_unchanged s f i⟩

/-- The complete output transfer test uses the entire literal opposite group. -/
theorem fixed_equality_binary_dictionary (B : Mat) :
    binaryTransport B*X=(2 : ℂ) • conjugate (B*X) ∧
    ((binaryTransport B).det≠0 ↔ B.det≠0) ∧
    (¬Direction (binaryTransport B*X) ↔ ¬groupDirection .icosahedral (B*X)) ∧
    (∀a b,binaryTransport B a b≠0 ↔ B a b≠0) :=
  ⟨binary_transfer_exact B,binary_nonsingular_iff B,outside_transfer_iff B,binary_support_iff B⟩

end
end Holant.Certificates.OppositeIcosahedral
