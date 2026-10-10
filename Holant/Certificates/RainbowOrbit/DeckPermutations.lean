import Holant.Certificates.RainbowOrbit.GeneratedOrbit
import Holant.Certificates.RainbowOrbit.MaximalLines
import Holant.Certificates.RainbowOrbit.ExternalDeckIntegration
import Mathlib.GroupTheory.OrderOfElement

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem FamilyDeckPoint.operation {G : BinaryMatrix→Prop} (hG : MatrixFamily G)
    {n : ℕ} (R : Fin n→BinaryMatrix) (hR : ∀i,G (R i))
    (o : Operation n) {p : Point} (hp : FamilyDeckPoint G p) :
    FamilyDeckPoint G (operationPoint R (fun i => hG.nonsingular (hR i)) o p) := by
  obtain ⟨r,F,hF,⟨U,V,hU,hV,rfl⟩,rfl⟩ := hp
  cases o with
  | dress j i =>
    let L := physicalSingleLeg j (R i)
    have hd : ∀q,(L q).det≠0 := singleLeg_det _ (hG.nonsingular (hR i)) j
    have hL : ∀q,G (L q) := by
      intro q
      by_cases h : q=j
      · simpa [L,physicalSingleLeg,h] using hR i
      · simpa [L,physicalSingleLeg,h] using hG.one
    refine ⟨r,act L (matchingTensor r U V),act_nonzero L hd hF,?_,rfl⟩
    have hm (a b : Fin 4) (M : BinaryMatrix) (hM : G M) : G (L a*M*(L b).transpose) :=
      hG.mul (hG.mul (hL a) hM) (hG.transpose (hL b))
    fin_cases r
    · exact ⟨_,_,hm 0 1 U hU,hm 2 3 V hV,act_P0 L U V⟩
    · exact ⟨_,_,hm 0 2 U hU,hm 1 3 V hV,act_P1 L U V⟩
    · exact ⟨_,_,hm 0 3 U hU,hm 1 2 V hV,act_P2 L U V⟩
  | swap j =>
    have hn : Tensor.reindex (adjacent j) (matchingTensor r U V)≠0 := by
      intro hz
      exact hF (portLinear_injective (adjacent j) hz)
    obtain ⟨S,T,hS,hT,he⟩ := adjacent_matching G (fun {U} h => hG.transpose h) j r U V hU hV
    exact ⟨adjacentLabels j r,_,hn,⟨S,T,hS,hT,he⟩,rfl⟩

def restrictPermutation (D : Finset Point) (e : Point↪Point) (hD : ∀p∈D,e p∈D) :
    Equiv.Perm {p : Point // p∈D} :=
  Equiv.ofBijective (fun p => ⟨e p,hD p p.property⟩)
    ⟨fun p q he => Subtype.ext (e.injective (congrArg Subtype.val he)),
      Finite.surjective_of_injective (fun p q he => Subtype.ext (e.injective (congrArg Subtype.val he)))⟩

theorem standard_deck_semantics (g : PlatonicModel) (p : Point) :
    FamilyDeckPoint (fun U => groupDirection g U) p ↔ p∈deck g := by
  constructor
  · rintro ⟨r,F,hF,⟨U,V,hU,hV,rfl⟩,rfl⟩
    exact (inDeck_iff_mem g _ hF).mp ⟨r,U,V,hU,hV,Proportional.refl _⟩
  · intro hm
    induction p using Projectivization.ind with | h F hF =>
    obtain ⟨r,U,V,hU,hV,⟨c,hc,he⟩⟩ := (inDeck_iff_mem g F hF).mpr hm
    exact ⟨r,F,hF,⟨c • U,V,groupDirection_smul g hU hc,hV,
      he.trans (matchingTensor_smul_left r c U V).symm⟩,rfl⟩

def standardOperationPermutation (g : PlatonicModel) (o : Operation (size g)) :
    Equiv.Perm {p : Point // p∈deck g} :=
  restrictPermutation (deck g) (operationPoint (representative g) (representative_det_ne_zero g) o)
    (fun p hp => (standard_deck_semantics g _).mp
      (((standard_deck_semantics g p).mpr hp).operation (standardMatrixFamily g)
        (representative g) (representative_mem g) o))

def standardGamma (g : PlatonicModel) : Subgroup (Equiv.Perm {p : Point // p∈deck g}) :=
  Subgroup.closure (Set.range (standardOperationPermutation g))

def markedOperationPermutation (f : Form) (o : Operation 24) :
    Equiv.Perm {p : Point // p∈markedDeck f} :=
  restrictPermutation (markedDeck f) (operationPoint (markedRepresentative f) (markedRepresentative_det f) o)
    (fun p hp => (markedDeck_iff_mem f _).mp
      (FamilyDeckPoint.operation (markedMatrixFamily f)
        (markedRepresentative f) (Direction.standard f) o ((markedDeck_iff_mem f p).mpr hp)))

def markedGamma (f : Form) : Subgroup (Equiv.Perm {p : Point // p∈markedDeck f}) :=
  Subgroup.closure (Set.range (markedOperationPermutation f))

def externalOperationPermutation (o : Operation 12) :
    Equiv.Perm {p : Point // p∈External.deck} :=
  restrictPermutation External.deck (operationPoint External.representative External.representative_det_ne_zero o)
    (fun p hp => (External.deckPoint_iff_mem _).mp
      (FamilyDeckPoint.operation External.matrixFamily
        External.representative External.Direction.representative o ((External.deckPoint_iff_mem p).mpr hp)))

def externalGamma : Subgroup (Equiv.Perm {p : Point // p∈External.deck}) :=
  Subgroup.closure (Set.range externalOperationPermutation)

/-- Every actual deck permutation group is finite. -/
theorem standardGamma_finite (g : PlatonicModel) : Finite (standardGamma g) := inferInstance
theorem markedGamma_finite (f : Form) : Finite (markedGamma f) := inferInstance
theorem externalGamma_finite : Finite externalGamma := inferInstance

end
end Holant.Certificates.RainbowOrbit
