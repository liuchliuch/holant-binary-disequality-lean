import Holant.Proofs.Hardness.EightVertexGaugeMixedPencil
import Holant.Proofs.Hardness.EightVertexGaugePhysicalOutcome
import Holant.Proofs.Hardness.EightVertexGaugeRepresentativeLines

/-! Mixed-row anchor comparison in the actual native family. Different fourth
powers yield an indexed nonzero binary outside the complete monomial group,
with exact same-family realization. The source rows, port permutations, cap
representative and scalar are retained; this is a resource, not hardness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeMixedPhysical
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
open EightVertexGaugePorts EightVertexGaugePhysicalOutcome EightVertexGaugeRepresentativeLines
open Holant.OpenNetworkComposition

theorem onPorts_actual_pair (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (M N : Signature AlgebraicComplex 4)
    (actualM : Gadget.Realizes F .disequality M) (actualN : Gadget.Realizes F .disequality N)
    (e f : Equiv.Perm (Fin 4)) (cross : Bool) : Gadget.Realizes F .disequality
      (EightVertexGaugeTwoRowNetwork.onPorts M N e f cross).denote := by
  have hr := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality M actualM e.symm
  have hs := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality N actualN f.symm
  simp only [Equiv.symm_symm] at hr hs
  have ht := Holant.OpenNetworkComposition.realizes_tensor F .disequality _ _ hr hs
  have hw := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _ ht
    (EightVertexGaugeTwoRowNetwork.order cross).symm
  simp only [Equiv.symm_symm] at hw
  have hc := realizes_contract_exact_of_identity F hI _
    (realizes_contract_exact_of_identity F hI _ hw)
  simpa only [EightVertexGaugeTwoRowNetwork.onPorts,EightVertexGaugeTwoRowNetwork.connect,
    Network.denote_contract,Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,
    Holant.Complexity.BinaryInterpolation.Chains.tensor_denote,Network.denote_corolla] using hc

theorem complex_onPorts (a b : AlgebraicComplex) (u v : Fin 4 → AlgebraicComplex)
    (e f : Equiv.Perm (Fin 4)) (cross : Bool) :
    complexTensor (EightVertexGaugeTwoRowNetwork.onPorts (weighted a u) (weighted b v) e f cross).denote =
      (EightVertexGaugeTwoRowNetwork.onPorts
        (weighted (a : ℂ) (fun j => (u j : ℂ)))
        (weighted (b : ℂ) (fun j => (v j : ℂ))) e f cross).denote := by
  rw [onPorts_output,onPorts_output,complex_output]

theorem physical_escape {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m) (a b : AlgebraicComplex)
    (u v : Fin 4 → AlgebraicComplex)
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (sameU : ∀ i, u i ^ 4 = u 0 ^ 4) (sameV : ∀ i, v i ^ 4 = v 0 ^ 4)
    (different : u 0 ^ 4 ≠ v 0 ^ 4)
    (actualM : Gadget.Realizes F .disequality (weighted a u))
    (actualN : Gadget.Realizes F .disequality (weighted b v)) :
    ∃ (e f : Equiv.Perm (Fin 4)) (cross : Bool)
      (order : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m),
      let q := (EightVertexGaugeTwoRowNetwork.onPorts (weighted a u) (weighted b v) e f cross).denote
      physicalCard q order (reps.matrix p t) ≠ 0 ∧
      physicalCard q order (reps.matrix p t) ∉ groupM m ∧
      Gadget.Realizes F .disequality (kernelSignature (physicalCard q order (reps.matrix p t))) := by
  obtain ⟨e,f,cross,bad⟩ := EightVertexGaugeMixedPencil.unsafe_deck hm (a : ℂ) (b : ℂ)
    (fun j => (u j : ℂ)) (fun j => (v j : ℂ))
    (by exact_mod_cast ha) (by exact_mod_cast hb)
    (fun j => by exact_mod_cast hu j) (fun j => by exact_mod_cast hv j)
    (fun j => by exact_mod_cast sameU j) (fun j => by exact_mod_cast sameV j)
    (by exact_mod_cast different)
  let q := (EightVertexGaugeTwoRowNetwork.onPorts (weighted a u) (weighted b v) e f cross).denote
  have fail : ¬ MonomialPhysicalDeck reps q := by
    intro good
    have safe := monomial_safeDeck hm reps q good
    rw [complex_onPorts] at safe
    exact bad safe
  unfold MonomialPhysicalDeck at fail
  push Not at fail
  obtain ⟨order,p,t,nonzero,outside⟩ := fail
  refine ⟨e,f,cross,order,p,t,nonzero,?_,?_⟩
  · exact fun hg => outside ((line_iff_group (by omega) F reps _).mpr hg)
  · exact physical_card_realizes F hI q
      (onPorts_actual_pair F hI _ _ actualM actualN e f cross) order _ (reps.actual p t)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeMixedPhysical
end
