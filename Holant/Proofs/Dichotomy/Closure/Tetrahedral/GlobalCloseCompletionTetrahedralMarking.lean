import Holant.Proofs.Closure.ClosureMarkedPlatonicSubgroup
import Holant.Projective.FiniteSubgroupClassification.NormalKlein

/-! Actual tetrahedral placement from the returned semantic marking.
The internal placement is literal T; the external placement keeps its no-Z
proof. Conjugation is used only in the group proof, never as a gadget label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralMarking
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Projective.FiniteSubgroupClassification
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient

/-- A literal subgroup equality. No conjugator or normal-form premise. -/
theorem a4_with_literal_marks (H : Subgroup (PGL2 ℂ))
    (e : H ≃* A4) (hx : xClass ∈ H) (hz : zClass ∈ H) :
    H = modelPGL .tetrahedral := by
  have hPH : pauliSubgroup ≤ H := by
    change Subgroup.closure _ ≤ H
    rw [Subgroup.closure_le]
    intro q hq
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · exact hx
    · have he : q = zClass := Set.mem_singleton_iff.mp hq
      exact he.symm ▸ hz
  let K := pauliSubgroup.subgroupOf H
  let k : K ≃* pauliSubgroup := Subgroup.subgroupOfEquivOfLe hPH
  letI : IsKleinFour K := {
    card_four := (Nat.card_congr k.toEquiv).trans pauli_card
    exponent_two := by
      rw [Monoid.exponent_eq_of_mulEquiv k]
      exact IsKleinFour.exponent_two }
  let ke : K ≃* K.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective K e.toMonoidHom e.injective
  letI : IsKleinFour (K.map e.toMonoidHom) := {
    card_four := (Nat.card_congr ke.symm.toEquiv).trans
      (IsKleinFour.card_four (G:=K))
    exponent_two := by
      rw [←Monoid.exponent_eq_of_mulEquiv ke]
      exact IsKleinFour.exponent_two }
  have hK : K.map e.toMonoidHom = a4KleinFour := a4_unique_kleinFour _
  have hKn : K.Normal := by
    apply Subgroup.Normal.of_map_injective (φ:=e.toMonoidHom) e.injective
    simpa only [hK] using a4_kleinFour_normal
  letI : (pauliSubgroup.subgroupOf H).Normal := hKn
  have hHO : H ≤ modelPGL .octahedral := by
    rw [←pauli_normalizer]
    exact Subgroup.le_normalizer_of_normal_subgroupOf hPH
  have hc : Nat.card H = 12 := by
    rw [Nat.card_congr e.toEquiv]
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact subgroup_octahedral_card_twelve H hHO hc


theorem model_equiv (H : Subgroup (PGL2 ℂ))
    (model : HasModel H (.platonic .tetrahedral)) : Nonempty (H ≃* A4) := by
  obtain ⟨g,hg⟩ := model
  let e := H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have e' : H.map (MulAut.conj g).toMonoidHom ≃* A4 := by
    rw [hg]
    exact tetrahedral_iso_A4
  exact ⟨e.trans e'⟩

theorem internal_literal (H : Subgroup (PGL2 ℂ))
    (model : HasModel H (.platonic .tetrahedral))
    (hx : xClass∈H) (hz : zClass∈H) : H=modelPGL .tetrahedral :=
  a4_with_literal_marks H (Classical.choice (model_equiv H model)) hx hz

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (identity : (⟨2,binarySignature (Signature.equality : Holant.Certificates.MatchingContractionClosure.Binary (K:=L))⟩ : AnySignature L)∈F)

theorem semantic_tetrahedral_actual
    (model : HasModel (overgroup phi F torsion) (.platonic .tetrahedral)) :
    group phi F torsion = overgroup phi F torsion := by
  have hc : Nat.card (overgroup phi F torsion) ≤ 2*Nat.card (group phi F torsion) := by
    rw [source_cardinal]
    exact cardinal_original phi F torsion
  obtain ⟨p,hp,g,hk,hh⟩ := ClosureMarkedPlatonicSubgroup.actual_model
    (group phi F torsion) (overgroup phi F torsion)
    (ClosureMarkedReversalOvergroup.actual_le _ _) hc .tetrahedral model
  have hp' : p=.tetrahedral := by
    rcases hp with hp | ⟨impossible,_⟩
    · exact hp
    · cases impossible
  subst p
  exact Subgroup.map_injective (MulAut.conj g).injective (hh.trans hk.symm)

include identity in
theorem semantic_tetrahedral_literal
    (model : HasModel (overgroup phi F torsion) (.platonic .tetrahedral)) :
    group phi F torsion = modelPGL .tetrahedral := by
  have same := semantic_tetrahedral_actual phi F torsion model
  have hz : zClass∈group phi F torsion := by
    rw [same,←ClosureMarkedReversalOvergroup.Ambient.native_mark]
    exact ClosureMarkedReversalOvergroup.mark_mem _ _
  exact internal_literal _ (same.symm ▸ model) (nativeX_mem phi F torsion identity) hz

include identity in
theorem actual_tetrahedral_internal
    (model : HasModel (group phi F torsion) (.platonic .tetrahedral))
    (hz : zClass∈group phi F torsion) :
    group phi F torsion = modelPGL .tetrahedral :=
  internal_literal _ model (nativeX_mem phi F torsion identity) hz


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralMarking
end
