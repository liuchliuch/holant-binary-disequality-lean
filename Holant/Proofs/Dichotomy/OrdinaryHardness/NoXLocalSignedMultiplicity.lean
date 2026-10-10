import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalSignedMultiplicityPhase
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalRankOneCriterion
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiOppositeCap

/-! Semantic transport from an actual systematic row to its canonical
opposite bundles, retaining all signed multiplicities and supported markings. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalSignedMultiplicity
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export NoXLocalSignedMultiplicityPhase (unitPhase localFactor original canonical constant gauge split gauge_affine)
end P
namespace O
export NoXWeightedAntiOppositeCap (opposite embedding)
end O
namespace U
export OrdinaryNegativeXUniversalResource (Kind)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {n : ℕ} (kind : U.Kind) {f : Signature AlgebraicComplex n}
variable (D : SystematicSupport f kind.rank) (ports : Fin n→Port kind.arity)
variable (chart : ∀x,word ports (kind.code x)=D.encode x)
variable (odd : ∀j b,Odd (NoXSeparateSignedProjection.signedCount ports j b))

private def twistChart (a : Word kind.rank) : SystematicSupport (localTwist (D.encode a) f) kind.rank where
  ports := D.ports
  injective := D.injective
  encode := D.encode
  affine := D.affine
  free := D.free
  supported x := (NoXLocalRankOneCriterion.twist_support f (D.encode a) _).mpr (D.supported x)
  covers x hx := D.covers x ((NoXLocalRankOneCriterion.twist_support f (D.encode a) _).mp hx)

include chart odd in
theorem reduced_twist_affine (a : Word kind.rank)
    (canonical : Affine (fun x=>P.canonical (kind.code a) (kind.code x)*D.reduced x)) :
    Affine (fun x=>localTwist (D.encode a) f (D.encode x)) := by
  have hg := (P.gauge_affine ports odd (kind.code a)).precompose kind.code kind.code_affine
  have hA := (hg.mul canonical).scale (P.constant ports)
  convert hA using 1
  funext x
  rw [localTwist_apply]
  have hp : (∏i,if D.encode a i && D.encode x i then zetaEight else 1)=
      P.original ports (kind.code a) (kind.code x) := by
    simp only [P.original,P.unitPhase,chart]
  rw [hp,P.split ports odd]
  simp only [SystematicSupport.reduced]
  ring

include chart odd in
theorem local_of_canonical_twists (square : Affine (fun x=>f x^2))
    (canonical : ∀a : Word kind.rank,Affine (fun x=>P.canonical (kind.code a) (kind.code x)*D.reduced x)) :
    LocalAffine f := by
  have nonzero : f≠0 := by intro hz;exact D.supported (origin _) (congrFun hz _)
  obtain ⟨S,hS⟩ := OrdinaryNegativeAffineSquareSupport.exists_support_system f square nonzero
  intro alpha supported
  let a : Word kind.rank := fun i=>alpha (D.ports i)
  have ha : D.encode a=alpha := D.covers alpha supported
  rw [←ha]
  apply (twistChart kind D a).affine_of_reduced S
  · intro x
    exact (hS x).trans (NoXLocalRankOneCriterion.twist_support f (D.encode a) x).symm
  · exact reduced_twist_affine kind D ports chart odd a (canonical a)

theorem canonical_eq_opposite (a x : Word kind.arity) :
    P.canonical a x=∏i : Fin (kind.arity+kind.arity),
      if O.opposite kind a i && O.opposite kind x i then zetaEight else 1 := by
  rw [Fin.prod_univ_add]
  simp only [O.opposite,Fin.addCases_left,Fin.addCases_right]
  unfold P.canonical
  simp only [Fintype.prod_bool,Finset.prod_mul_distrib]
  have positive : (∏j,P.localFactor a x j false)=∏j,if a j && x j then zetaEight else 1 := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [P.localFactor,P.unitPhase]
    cases a j <;> cases x j <;> rfl
  have negative : (∏j,P.localFactor a x j true)=∏j,if !(a j) && !(x j) then zetaEight else 1 := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [P.localFactor,P.unitPhase]
    cases a j <;> cases x j <;> rfl
  rw [positive,negative]
  ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalSignedMultiplicity
end
