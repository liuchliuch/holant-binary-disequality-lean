import Holant.Proofs.Closure.ClosureMarkedReversalIndex
import Holant.Proofs.Closure.ClosureMarkedSourceRouting
import Holant.Projective.FiniteGroupFacts.ModelInclusions

/-! NEW_POST_RECOVERY; pending strict check. Exact source subgroup dispatch
inside the constructed semantic T/O/I overgroup. Frozen no-index-two and
unique-index-two group facts are reused; no Platonic algorithm, physical basis
or complexity result is asserted. The SAME semantic conjugacy is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedPlatonicSubgroup
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteSubgroupClassification
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2
open Holant.LocalDrafts.FinitePGL2.Stabilization

theorem index_one_or_two {G : Type*} [Group G] [Finite G] (S : Subgroup G)
    (hi : S.index ≤ 2) : S.index = 1 ∨ S.index = 2 := by
  have hp : S.index ≠ 0 := S.index_ne_zero_of_finite
  omega

theorem no_index_two_tetrahedral (S : Subgroup (modelPGL .tetrahedral)) : S.index ≠ 2 := by
  have hn := a4_no_index_two (S.map tetrahedral_iso_A4.toMonoidHom)
  rwa [Subgroup.index_map_of_bijective tetrahedral_iso_A4.bijective] at hn

theorem no_index_two_icosahedral (S : Subgroup (modelPGL .icosahedral)) : S.index ≠ 2 := by
  have hn := a5_no_index_two (S.map icosahedral_iso_A5.toMonoidHom)
  rwa [Subgroup.index_map_of_bijective icosahedral_iso_A5.bijective] at hn

theorem full_of_no_index_two (J K : Subgroup (PGL2 ℂ)) [Finite K] (hle : J ≤ K)
    (hi : (J.subgroupOf K).index ≤ 2) (hn : (J.subgroupOf K).index ≠ 2) : J = K := by
  have hone : (J.subgroupOf K).index = 1 := (index_one_or_two _ hi).resolve_right hn
  have hk : K ≤ J := (Subgroup.relIndex_eq_one).mp hone
  exact le_antisymm hle hk

theorem octahedral_index_two (J : Subgroup (PGL2 ℂ)) (hle : J ≤ modelPGL .octahedral)
    (hi : (J.subgroupOf (modelPGL .octahedral)).index = 2) : J = modelPGL .tetrahedral := by
  let S := J.subgroupOf (modelPGL .octahedral)
  let T := (modelPGL .tetrahedral).subgroupOf (modelPGL .octahedral)
  have hs : (S.map octahedral_iso_S4.toMonoidHom).index = 2 := by
    rw [Subgroup.index_map_of_bijective octahedral_iso_S4.bijective]
    exact hi
  have ht : (T.map octahedral_iso_S4.toMonoidHom).index = 2 := by
    rw [Subgroup.index_map_of_bijective octahedral_iso_S4.bijective]
    exact tetrahedral_index_in_octahedral
  have he : S.map octahedral_iso_S4.toMonoidHom = T.map octahedral_iso_S4.toMonoidHom :=
    (s4_unique_index_two _ hs).trans (s4_unique_index_two _ ht).symm
  have hst : S = T := Subgroup.map_injective octahedral_iso_S4.injective he
  have h := Subgroup.subgroupOf_inj.mp hst
  simpa only [inf_eq_left.mpr hle,inf_eq_left.mpr tetrahedral_le_octahedral] using h

theorem subgroup_model_index (J : Subgroup (PGL2 ℂ)) (p : PlatonicModel)
    (hle : J ≤ modelPGL p) (hc : Nat.card (modelPGL p) ≤ 2*Nat.card J) :
    (J.subgroupOf (modelPGL p)).index ≤ 2 := by
  letI : Finite J := Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
  have hs : Nat.card (J.subgroupOf (modelPGL p)) = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hm := (J.subgroupOf (modelPGL p)).index_mul_card
  rw [hs] at hm
  rw [← hm] at hc
  exact Nat.le_of_mul_le_mul_right hc Nat.card_pos

/-- Every group of index at most two in a displayed Platonic model is
identified exactly. O's genuine T alternative is preserved. -/
theorem subgroup_model (J : Subgroup (PGL2 ℂ)) (p : PlatonicModel)
    (hle : J ≤ modelPGL p) (hi : (J.subgroupOf (modelPGL p)).index ≤ 2) :
    J = modelPGL p ∨ (p = .octahedral ∧ J = modelPGL .tetrahedral) := by
  cases p with
  | tetrahedral => exact Or.inl (full_of_no_index_two _ _ hle hi (no_index_two_tetrahedral _))
  | icosahedral => exact Or.inl (full_of_no_index_two _ _ hle hi (no_index_two_icosahedral _))
  | octahedral =>
      rcases index_one_or_two _ hi with hone | htwo
      · exact Or.inl (full_of_no_index_two _ _ hle hi (by omega))
      · exact Or.inr ⟨rfl,octahedral_index_two J hle htwo⟩

/-- The actual source subgroup uses the SAME ambient conjugator as its
semantic overgroup. This establishes a literal actual-H model, not only an
abstract group isomorphism or an overgroup model tag. -/
theorem actual_model (H K : Subgroup (PGL2 ℂ)) (hle : H ≤ K)
    (hcard : Nat.card K ≤ 2*Nat.card H) (p : PlatonicModel)
    (hk : HasModel K (.platonic p)) :
    ∃ q : PlatonicModel, (q = p ∨ (p = .octahedral ∧ q = .tetrahedral)) ∧
      ∃ g : PGL2 ℂ, K.map (MulAut.conj g).toMonoidHom = modelPGL p ∧
        H.map (MulAut.conj g).toMonoidHom = modelPGL q := by
  obtain ⟨g,hg⟩ := hk
  let J := H.map (MulAut.conj g).toMonoidHom
  have hj : J ≤ modelPGL p := by
    rintro x ⟨y,hy,rfl⟩
    rw [← hg]
    exact ⟨y,hle hy,rfl⟩
  have hc : Nat.card (modelPGL p) ≤ 2*Nat.card J := by
    rw [← hg,card_conjugate_subgroup,card_conjugate_subgroup]
    exact hcard
  rcases subgroup_model J p hj (subgroup_model_index J p hj hc) with he | ⟨hp,he⟩
  · exact ⟨p,Or.inl rfl,g,hg,he⟩
  · exact ⟨.tetrahedral,Or.inr ⟨hp,rfl⟩,g,hg,he⟩

namespace Source
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient
variable {L : Type*} [Field L] [NumberField L]

/-- The original source family fixes actual H, semantic K and their bound.
Only the actual returned semantic branch proof is consumed here. -/
theorem actual_model (phi : L →+* Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (p : PlatonicModel) (semantic : HasModel (overgroup phi F torsion) (.platonic p)) :
    ∃ q : PlatonicModel, (q = p ∨ (p = .octahedral ∧ q = .tetrahedral)) ∧
      HasModel (group phi F torsion) (.platonic q) := by
  have hc : Nat.card (overgroup phi F torsion) ≤ 2*Nat.card (group phi F torsion) := by
    rw [ClosureMarkedDihedral.Source.source_cardinal]
    exact cardinal_original phi F torsion
  obtain ⟨q,hq,g,hk,hh⟩ := ClosureMarkedPlatonicSubgroup.actual_model
    (group phi F torsion) (overgroup phi F torsion)
    (ClosureMarkedReversalOvergroup.actual_le _ _) hc p semantic
  exact ⟨q,hq,g,hh⟩

/-- Actual-source model data selected from the genuine semantic payload.
The model tag always applies to H, with the allowed O-to-T distinction recorded. -/
structure ActualModel (phi : L →+* Scalar) (F : SignatureFamily L)
    (torsion : ResidualTorsion F) (semanticType : PlatonicModel) where
  actualType : PlatonicModel
  relation : actualType = semanticType ∨
    (semanticType = .octahedral ∧ actualType = .tetrahedral)
  actual : HasModel (group phi F torsion) (.platonic actualType)

def resolve (phi : L →+* Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (p : PlatonicModel) (semantic : HasModel (overgroup phi F torsion) (.platonic p)) :
    ActualModel phi F torsion p := by
  let receipt := actual_model phi F torsion p semantic
  let q := Classical.choose receipt
  have hq := Classical.choose_spec receipt
  exact ⟨q,hq.1,hq.2⟩

def ActualFor (phi : L →+* Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F) :
    ClosureMarkedSourceRouting.Marking phi F torsion → Type
  | .platonic p _ => ActualModel phi F torsion p
  | _ => PUnit

def refine (phi : L →+* Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (M : ClosureMarkedSourceRouting.Marking phi F torsion) : ActualFor phi F torsion M :=
  match M with
  | .platonic p semantic => resolve phi F torsion p semantic
  | .smallTwo _ => PUnit.unit
  | .smallFour _ _ => PUnit.unit
  | .cyclic _ => PUnit.unit
  | .monomial _ => PUnit.unit
  | .bilinear _ => PUnit.unit
  | .unshifted _ _ _ => PUnit.unit
  | .shifted _ _ _ _ _ _ _ => PUnit.unit

/-- Closed actual-family producer. No source or semantic model, classifier,
conjugator, phase or desired branch is caller input. Existing native payloads
are preserved and a semantic Platonic payload is resolved to actual H. -/
def produce (phi : L →+* Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (equality : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F) :
    Σ M : ClosureMarkedSourceRouting.Marking phi F torsion, ActualFor phi F torsion M :=
  let M := ClosureMarkedSourceRouting.produce phi F torsion equality
  ⟨M,refine phi F torsion M⟩

end Source
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedPlatonicSubgroup
end
