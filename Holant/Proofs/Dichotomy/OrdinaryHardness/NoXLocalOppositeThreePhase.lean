import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiOppositeCap
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoAlphaCore

/-! The all-opposite rank-two source phase test. The six original ordered
ports and all four supported local twists are retained literally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalOppositeThreePhase
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open scoped BigOperators
namespace O
export NoXWeightedAntiOppositeCap (embedding)
end O
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
  (Full CommonFourth Cross SignedCross full_affine_iff)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
abbrev embed : (Fin 2→Bool)→(Fin 6→Bool) := O.embedding .three
def project (z : Fin 6→Bool) : Fin 2→Bool := ![z 0,z 1]

theorem embed_vector (x : Fin 2→Bool) :
    embed x=![x 0,x 1,x 0^^x 1,!(x 0),!(x 1),!(x 0^^x 1)] := by
  funext i
  fin_cases i <;> rfl

theorem project_affine : TwoTranslate.IsAffineMap project := by
  have he : project=(fun z : Fin 6→Bool=>fun i : Fin 2=>z ((![0,1] : Fin 2→Fin 6) i)) := by
    funext z i
    fin_cases i <;> rfl
  rw [he]
  exact coordinates_isAffineMap _

theorem project_embed (x : Fin 2→Bool) : project (embed x)=x := by
  funext i
  fin_cases i <;> rfl

def system : AffineSystem 6 where
  rows := 4
  matrix := ![![1,1,1,0,0,0],![1,0,0,1,0,0],![0,1,0,0,1,0],![0,0,1,0,0,1]]
  rhs := ![0,1,1,1]

theorem system_holds (z : Fin 6→Bool) : system.Holds z ↔ z=embed (project z) := by
  revert z
  decide

def lift (h : Signature AlgebraicComplex 2) : Signature AlgebraicComplex 6 :=
  fun z=>if z=embed (project z) then h (project z) else 0

@[simp] theorem lift_embed (h : Signature AlgebraicComplex 2) (x : Fin 2→Bool) :
    lift h (embed x)=h x := by simp [lift,project_embed]

theorem affine_lift {h : Signature AlgebraicComplex 2} (affine : Affine h) : Affine (lift h) := by
  have hA := (affine.precompose project project_affine).restrict system
  convert hA using 1
  funext z
  simp only [lift,system_holds]

def phase (a x : Fin 2→Bool) : AlgebraicComplex :=
  ∏j : Fin 6,if embed a j && embed x j then zetaEight else 1

theorem phase_formula (a x : Fin 2→Bool) :
    phase a x=zetaEight*(if x=a then imaginaryUnit else 1) := by
  have ae : a=![a 0,a 1] := by funext i;fin_cases i <;> rfl
  have xe : x=![x 0,x 1] := by funext i;fin_cases i <;> rfl
  rw [ae,xe]
  cases a 0 <;> cases a 1 <;> cases x 0 <;> cases x 1 <;>
    simp [phase,embed_vector,Fin.prod_univ_succ,funext_iff,Fin.forall_fin_succ]
  all_goals exact Or.inl (by simpa only [pow_two] using zetaEight_sq)

theorem phase_nonzero (a x : Fin 2→Bool) : phase a x≠0 := by
  rw [phase_formula]
  apply mul_ne_zero zetaEight_ne_zero
  split_ifs
  · intro zero
    have hs := imaginaryUnit_sq
    rw [zero] at hs
    norm_num at hs
  · exact one_ne_zero

theorem phase_fourth (a x : Fin 2→Bool) : phase a x^4= -1 := by
  rw [phase_formula,mul_pow,zetaEight_pow_four]
  split_ifs <;> simp [imaginaryUnit_pow_four]

theorem phase_cross (a : Fin 2→Bool) :
    (phase a ![false,false]*phase a ![true,true])^2=
      -(phase a ![false,true]*phase a ![true,false])^2 := by
  have ae : a=![a 0,a 1] := by funext i;fin_cases i <;> rfl
  rw [ae]
  cases a 0 <;> cases a 1 <;>
    simp [phase_formula,funext_iff,Fin.forall_fin_succ,mul_pow,zetaEight_sq,imaginaryUnit_sq]

theorem negative_cross (h : Signature AlgebraicComplex 2) (full : B.Full h)
    (fourth : B.CommonFourth h) (bad : ¬Affine h) :
    (h ![false,false]*h ![true,true])^2= -(h ![false,true]*h ![true,false])^2 := by
  have eq4 : ((h ![false,false]*h ![true,true])^2)^2=
      ((h ![false,true]*h ![true,false])^2)^2 := by
    simp only [←pow_mul,mul_pow]
    norm_num only [Nat.reduceMul]
    rw [fourth ![true,true],fourth ![false,true],fourth ![true,false]]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp eq4 with positive|negative
  · exact False.elim (bad ((B.full_affine_iff h full).mpr
      ⟨fourth,sq_eq_sq_iff_eq_or_eq_neg.mp positive⟩))
  · exact negative

theorem phase_affine (h : Signature AlgebraicComplex 2) (full : B.Full h)
    (fourth : B.CommonFourth h) (bad : ¬Affine h) (a : Fin 2→Bool) :
    Affine (fun x=>phase a x*h x) := by
  apply (B.full_affine_iff _ (fun x=>mul_ne_zero (phase_nonzero a x) (full x))).mpr
  constructor
  · intro x
    simp only [mul_pow,phase_fourth]
    rw [fourth x]
  · apply sq_eq_sq_iff_eq_or_eq_neg.mp
    change ((phase a ![false,false]*h ![false,false])*(phase a ![true,true]*h ![true,true]))^2=
      ((phase a ![false,true]*h ![false,true])*(phase a ![true,false]*h ![true,false]))^2
    calc
      _=(phase a ![false,false]*phase a ![true,true])^2*
        (h ![false,false]*h ![true,true])^2 := by ring
      _=(phase a ![false,true]*phase a ![true,false])^2*
        (h ![false,true]*h ![true,false])^2 := by rw [phase_cross,negative_cross h full fourth bad];ring
      _=_ := by ring

theorem local_twist (h : Signature AlgebraicComplex 2) (a : Fin 2→Bool) :
    localTwist (embed a) (lift h)=lift (fun x=>phase a x*h x) := by
  funext z
  by_cases hz : z=embed (project z)
  · simp only [localTwist_apply,lift,ite_eq_left hz]
    rw [hz]
    simp only [project_embed,phase]
  · simp only [localTwist_apply,lift,ite_eq_right hz,mul_zero]

theorem local_of_nonAffine (h : Signature AlgebraicComplex 2) (full : B.Full h)
    (fourth : B.CommonFourth h) (bad : ¬Affine h) : LocalAffine (lift h) := by
  intro z supported
  have hz : z=embed (project z) := by
    by_contra neg
    exact supported (by simp [lift,neg])
  rw [hz,local_twist]
  exact affine_lift (phase_affine h full fourth bad _)

theorem affine_of_not_local (h : Signature AlgebraicComplex 2) (full : B.Full h)
    (fourth : B.CommonFourth h) (bad : ¬LocalAffine (lift h)) : Affine h := by
  by_contra negative
  exact bad (local_of_nonAffine h full fourth negative)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalOppositeThreePhase
end
