import Holant.Platonic.RankDeficientLocalization.RichLine
import Holant.Platonic.FixedMatchingRuling.ReconstructionSource
import Holant.Pauli.ExoticKlein.EdgeCoordinates

/-! A common literal residual matching gives the actual fixed-block Segre cone.
Different edge enumerations and endpoint orientations are reconstructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RankDeficientLocalization
open Holant Holant.Pauli.ExoticKlein
open Holant.Certificates.MatchingContractionClosure
open Holant.Platonic.RainbowLocalization
open scoped BigOperators
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Literal matching blocks with two physical ports each. -/
def matchingBlockPorts (M : Presentation ℂ P) : ((e : Fin M.edges) × Fin 2) ≃ P :=
  (Equiv.sigmaEquivProd _ _).trans
    ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv).trans M.ports)

def matchingBlockAssignment (M : Presentation ℂ P)
    (x : Fin M.edges→Fin 2→Bool) : P→Bool :=
  fun p => x ((matchingBlockPorts M).symm p).1 ((matchingBlockPorts M).symm p).2

@[simp] theorem matchingBlockAssignment_port (M : Presentation ℂ P)
    (x : Fin M.edges→Fin 2→Bool) (e : Fin M.edges) (b : Bool) :
    matchingBlockAssignment M x (M.ports (e,b)) = x e (finTwoEquiv.symm b) := by
  simp [matchingBlockAssignment,matchingBlockPorts]

def sameMatchingCoordinates (M N : Presentation ℂ P)
    (hm : (presentationMatching M).mate=(presentationMatching N).mate) :
    (presentationMatching N).PairCoordinates (Fin M.edges) where
  ports := M.ports
  paired e b := by rw [←hm]; exact (presentationMatching M).mate_port e b

/-- Arbitrary oriented endpoint factors are reindexed by a genuine edge bijection. -/
theorem sameMatching_product (M N : Presentation ℂ P)
    (hm : (presentationMatching M).mate=(presentationMatching N).mate)
    (x : P→Bool) :
    N.tensor x = N.scalar * ∏e : Fin M.edges,
      let C := sameMatchingCoordinates M N hm
      let a := x (M.ports (e,false))
      let b := x (M.ports (e,true))
      if C.reverse e then N.matrix (C.edges e) b a else N.matrix (C.edges e) a b := by
  let C := sameMatchingCoordinates M N hm
  change N.scalar * (∏e : Fin N.edges,N.matrix e (x (N.ports (e,false))) (x (N.ports (e,true)))) = _
  rw [←Equiv.prod_comp C.edges]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  change N.matrix (C.edges e) (x (N.ports (C.edges e,false))) (x (N.ports (C.edges e,true))) = _
  change _ = if C.reverse e then N.matrix (C.edges e) (x (C.ports (e,true))) (x (C.ports (e,false)))
    else N.matrix (C.edges e) (x (C.ports (e,false))) (x (C.ports (e,true)))
  rw [C.ports_false,C.ports_true]
  cases h : C.reverse e <;> simp [h,Matching.PairCoordinates.edges_apply,presentationMatching]

/-- Every presentation with the same physical mate involution is a pure
array in the fixed residual two-port blocks, including arbitrary scales. -/
theorem sameMatching_pure (M N : Presentation ℂ P)
    (hM : 0<M.edges)
    (hm : (presentationMatching M).mate=(presentationMatching N).mate) :
    FixedMatchingRuling.Segre.IsPureOrZero
      (fun x => N.tensor (matchingBlockAssignment M x)) := by
  let C := sameMatchingCoordinates M N hm
  let V : Fin M.edges→(Fin 2→Bool)→ℂ := fun e z =>
    if C.reverse e then N.matrix (C.edges e) (z 1) (z 0)
      else N.matrix (C.edges e) (z 0) (z 1)
  have he : (fun x => N.tensor (matchingBlockAssignment M x)) =
      N.scalar • FixedMatchingRuling.Segre.product V := by
    funext x
    rw [sameMatching_product M N hm]
    change N.scalar * _ = N.scalar * _
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    simp only [matchingBlockAssignment_port]
    rfl
  rw [he]
  exact Or.inr ⟨Function.update V ⟨0,hM⟩ (N.scalar • V ⟨0,hM⟩),
    (FixedMatchingRuling.Segre.product_smul_update V ⟨0,hM⟩ N.scalar).symm⟩

end Holant.Platonic.RankDeficientLocalization
