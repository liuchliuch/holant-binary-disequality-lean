import Holant.Proofs.Hardness.EightVertexGaugeFlipPairAlgebra
import Holant.Proofs.Hardness.EightVertexGaugePhysicalOutcome

/-! The two-I test closes the identity-vertex compatibility gap. Six actual
two-copy decks are tested: three for the original row and three after flipping
ports 2 and 3 by two retained I vertices. If all are safe, one diagonal basis
handles M, retained I, and native X. Otherwise an actual bad binary is supplied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeFlipPairOutcome
open Holant Holant.Tractable Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
open EightVertexGaugePorts EightVertexGaugeAffine EightVertexGaugePhysicalOutcome
open Holant.OpenNetworkComposition

def selected (M : Signature AlgebraicComplex 4) (flip : Bool) (i : Fin 3) :
    Signature AlgebraicComplex 4 :=
  let V := if flip then EightVertexGaugeFlipPairNetwork.value M else M
  (EightVertexGaugeTwoRowNetwork.onPorts V V (zeroPair i) (zeroPair i) true).denote

theorem selected_false (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex) (i : Fin 3) :
    selected (weighted a u) false i = row a u i := rfl

theorem selected_true (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex)
    (hu : ∀ i, u i ≠ 0) (i : Fin 3) :
    selected (weighted a u) true i =
      row (a*u 2*u 3) (EightVertexGaugeFlipPairAlgebra.weights u) i := by
  simp only [selected,ite_true,EightVertexGaugeFlipPairAlgebra.value a u hu,row]

/-- Actual substitution into the one-M/two-I/two-X graph. Both ordinary
closures consume retained I through the existing exact-normalization theorem. -/
theorem flip_actual (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (M : Signature AlgebraicComplex 4) (actual : Gadget.Realizes F .disequality M) :
    Gadget.Realizes F .disequality (EightVertexGaugeFlipPairNetwork.value M) := by
  have hi : Gadget.Realizes F .disequality EightVertexGaugeFlipPairNetwork.identity :=
    Gadget.realizes_of_mem F .disequality _ hI
  have hp := Holant.OpenNetworkComposition.realizes_tensor F .disequality _ _ hi hi
  have hp' := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _ hp
    (Equiv.swap (1 : Fin 4) 2).symm
  simp only [Equiv.symm_symm] at hp'
  have ht := Holant.OpenNetworkComposition.realizes_tensor F .disequality _ _ actual hp'
  have hw := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _ ht
    (EightVertexGaugeTwoRowNetwork.order false).symm
  simp only [Equiv.symm_symm] at hw
  have hc := realizes_contract_exact_of_identity F hI _
    (realizes_contract_exact_of_identity F hI _ hw)
  rw [← EightVertexGaugeFlipPairNetwork.denote]
  simpa only [EightVertexGaugeFlipPairNetwork.network,EightVertexGaugeTwoRowNetwork.connect,
    Network.denote_contract,Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,
    Holant.Complexity.BinaryInterpolation.Chains.tensor_denote,Network.denote_corolla,
    EightVertexGaugeFlipPairNetwork.identityPair] using hc

/-- There is one shared final basis, including the original row and both
literal resource types. The right branch keeps the flip choice and cap order. -/
theorem basis_with_identity_or_physical_escape {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m) (a : AlgebraicComplex)
    (u : Fin 4 → AlgebraicComplex) (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0)
    (actualM : Gadget.Realizes F .disequality (weighted a u)) :
    IsCommonKBasis affineClass
      {⟨4,weighted a u⟩,⟨2,kernelSignature Signature.equality⟩}
      (diagonalBasis (u 0) (hu 0)) ∨
      ∃ (flip : Bool) (i : Fin 3) (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m),
        physicalCard (selected (weighted a u) flip i) e (reps.matrix p t) ≠ 0 ∧
        ¬ ActualMonomialLine reps (physicalCard (selected (weighted a u) flip i) e (reps.matrix p t)) ∧
        Gadget.Realizes F .disequality
          (kernelSignature (physicalCard (selected (weighted a u) flip i) e (reps.matrix p t))) := by
  classical
  by_cases original : ∀ i : Fin 3, MonomialPhysicalDeck reps (row a u i)
  · let v := EightVertexGaugeFlipPairAlgebra.weights u
    have hv : ∀ i, v i ≠ 0 := EightVertexGaugeFlipPairAlgebra.weights_nonzero u hu
    have ha' : a*u 2*u 3 ≠ 0 := mul_ne_zero (mul_ne_zero ha (hu 2)) (hu 3)
    have hactual : Gadget.Realizes F .disequality (weighted (a*u 2*u 3) v) := by
      rw [← EightVertexGaugeFlipPairAlgebra.value a u hu]
      exact flip_actual F hI _ actualM
    by_cases flipped : ∀ i : Fin 3, MonomialPhysicalDeck reps (row (a*u 2*u 3) v i)
    · have h0 := physical_decks_fourths hm F reps a u ha hu original
      have h1 := physical_decks_fourths hm F reps (a*u 2*u 3) v ha' hv flipped
      have h8 := EightVertexGaugeFlipPairAlgebra.eighth_power u (hu 0) h0 h1
      exact Or.inl (row_identity_basis a u (hu 0) h0 h8)
    · obtain ⟨i,e,p,t,hn,ho,hr⟩ := escape_of_not_decks F hI reps _ v hactual flipped
      refine Or.inr ⟨true,i,e,p,t,?_,?_,?_⟩
      · simpa only [selected_true a u hu i] using hn
      · simpa only [selected_true a u hu i] using ho
      · simpa only [selected_true a u hu i] using hr
  · obtain ⟨i,e,p,t,hn,ho,hr⟩ := escape_of_not_decks F hI reps a u actualM original
    exact Or.inr ⟨false,i,e,p,t,hn,ho,hr⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeFlipPairOutcome
end
