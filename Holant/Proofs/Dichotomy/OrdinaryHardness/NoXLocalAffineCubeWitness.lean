import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalSignedMultiplicity
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineThreeFaces

/-! A genuine LocalAffine failure is witnessed by a supported marker and
one coordinate three-cube on the actual systematic support. At rank>=5,
the marker and entire cube share either a fixed coordinate or a signed pair
identification outside its directions. This is the combinatorial descent
boundary, not a claim that an unproved gadget/classifier already exists. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalAffineCubeWitness
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {n r : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)

def twistChart (a : Word r) : SystematicSupport (localTwist (D.encode a) f) r where
  ports := D.ports
  injective := D.injective
  encode := D.encode
  affine := D.affine
  free := D.free
  supported x := (NoXLocalRankOneCriterion.twist_support f (D.encode a) _).mpr (D.supported x)
  covers x hx := D.covers x ((NoXLocalRankOneCriterion.twist_support f (D.encode a) _).mp hx)

theorem witness (square : Affine (fun x=>f x^2)) (bad : ¬LocalAffine f) :
    ∃a z : Word r,∃i j k : Fin r,
      thirdRatio (fun x=>localTwist (D.encode a) f (D.encode x)) z (basis i) (basis j) (basis k)≠1 := by
  classical
  obtain ⟨alpha,supported,negative⟩ : ∃alpha,∃_ : f alpha≠0,¬Affine (localTwist alpha f) := by
    simpa only [LocalAffine,not_forall,not_imp] using bad
  let a : Word r := fun i=>alpha (D.ports i)
  have ha : D.encode a=alpha := D.covers alpha supported
  have nonzero : f≠0 := by intro zero;exact supported (congrFun zero alpha)
  obtain ⟨S,hS⟩ := OrdinaryNegativeAffineSquareSupport.exists_support_system f square nonzero
  have reduced_bad : ¬Affine (fun x=>localTwist (D.encode a) f (D.encode x)) := by
    intro good
    apply negative
    rw [←ha]
    apply (twistChart D a).affine_of_reduced S
    · intro x
      exact (hS x).trans (NoXLocalRankOneCriterion.twist_support f (D.encode a) x).symm
    · exact good
  have full : ∀x,localTwist (D.encode a) f (D.encode x)≠0 := (twistChart D a).supported
  have failed : ¬∀z i j k,thirdRatio (fun x=>localTwist (D.encode a) f (D.encode x))
      z (basis i) (basis j) (basis k)=1 := by
    intro cubes
    exact reduced_bad (OrdinaryNegativeAffineThreeFaces.affine_of_coordinate_cubes _ full cubes)
  push Not at failed
  obtain ⟨z,i,j,k,h⟩ := failed
  exact ⟨a,z,i,j,k,h⟩

/-- The two outside coordinates give an actual equality or inequality
relation obeyed by both the support marker and every cube corner. -/
theorem pin_or_signed_pair (higher : 5≤r) (a z : Word r) (i j k : Fin r) :
    (∃p : Fin r,p∉({i,j,k} : Finset (Fin r)) ∧ a p=z p) ∨
    (∃p q : Fin r,p∉({i,j,k} : Finset (Fin r)) ∧ q∉({i,j,k} : Finset (Fin r)) ∧
      p≠q ∧ (a p ^^ a q)=(z p ^^ z q)) := by
  classical
  by_cases pin : ∃p : Fin r,p∉({i,j,k} : Finset (Fin r)) ∧ a p=z p
  · exact Or.inl pin
  right
  have size : ({i,j,k} : Finset (Fin r)).card≤3 := by
    exact (Finset.card_insert_le _ _).trans (by
      have h := Finset.card_insert_le j ({k} : Finset (Fin r))
      simpa using Nat.add_le_add_right h 1)
  have large : 1<(({i,j,k} : Finset (Fin r))ᶜ).card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨p,hp,q,hq,distinct⟩ := Finset.one_lt_card.mp large
  have hp' : p∉({i,j,k} : Finset (Fin r)) := Finset.mem_compl.mp hp
  have hq' : q∉({i,j,k} : Finset (Fin r)) := Finset.mem_compl.mp hq
  have ap : a p≠z p := fun equal=>pin ⟨p,hp',equal⟩
  have aq : a q≠z q := fun equal=>pin ⟨q,hq',equal⟩
  refine ⟨p,q,hp',hq',distinct,?_⟩
  have pair : ∀a b c d : Bool,a≠b→c≠d→(a ^^ c)=(b ^^ d) := by decide
  exact pair _ _ _ _ ap aq


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalAffineCubeWitness
end
