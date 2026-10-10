import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXAffineEmbeddingLift
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankThreeAlphaCore

/-! The genuine seven-opposite rank-three phase cancellation. Proper faces
and the Affine square are explicit source invariants; no local class oracle
or physical compression gate is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalOppositeSevenPhase
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open scoped BigOperators
namespace O
export NoXWeightedAntiOppositeCap (embedding embedding_affine)
end O
namespace A
export OrdinaryNegativeSparseMixingAlpha (phaseSeven phaseSeven_formula codeSeven twist_nonzero)
end A
namespace R
export OrdinaryNegativeRankThreeAlphaCore
  (cubicRatio distinct_cube_ratio origin_cube_ratio thirdRatio_square thirdRatio_mul phaseSeven_cubes)
end R
namespace F
export OrdinaryNegativeAffineThreeFaces (face cube_of_affine_face affine_of_coordinate_cubes)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
abbrev embed : Word 3→Word 14 := O.embedding .seven
def project (z : Word 14) : Word 3 := ![z 0,z 1,z 2]
theorem project_embed (x : Word 3) : project (embed x)=x := by
  funext i
  fin_cases i <;> rfl

theorem project_affine : TwoTranslate.IsAffineMap project := by
  have he : project=(fun z : Word 14=>fun i : Fin 3=>z ((![0,1,2] : Fin 3→Fin 14) i)) := by
    funext z i
    fin_cases i <;> rfl
  rw [he]
  exact coordinates_isAffineMap _

def lift := NoXAffineEmbeddingLift.lift embed project
@[simp] theorem lift_embed (h : Signature AlgebraicComplex 3) (x : Word 3) : lift h (embed x)=h x := by
  simp [lift,NoXAffineEmbeddingLift.lift,project_embed]
theorem affine_lift {h : Signature AlgebraicComplex 3} (affine : Affine h) : Affine (lift h) :=
  NoXAffineEmbeddingLift.affine_lift embed project (O.embedding_affine .seven) project_affine affine

theorem translated_ratio (u : Signature AlgebraicComplex 3) (a z v w t : Word 3) :
    thirdRatio (fun x=>u (xor x a)) z v w t=thirdRatio u (xor z a) v w t := by
  have shift (x y : Word 3) : xor (xor x y) a=xor (xor x a) y := by
    rw [xor_assoc,xor_comm y a,←xor_assoc]
  simp only [thirdRatio,shift]

def multiplier (a x : Word 3) : AlgebraicComplex := A.phaseSeven (xor x a)*A.phaseSeven x

theorem multiplier_affine (a : Word 3) : Affine (multiplier a) := by
  apply F.affine_of_coordinate_cubes _ (fun x=>mul_ne_zero
    (A.twist_nonzero (A.codeSeven (xor x a))) (A.twist_nonzero (A.codeSeven x)))
  intro z i j k
  change thirdRatio (fun x=>A.phaseSeven (xor x a)*A.phaseSeven x) z (basis i) (basis j) (basis k)=1
  rw [R.thirdRatio_mul,translated_ratio,R.phaseSeven_cubes,R.phaseSeven_cubes]
  split_ifs <;> norm_num

theorem phase_square (x : Word 3) : A.phaseSeven x^2=1 := by
  rw [A.phaseSeven_formula]
  split_ifs <;> norm_num

variable (h : Signature AlgebraicComplex 3) (full : ∀x,h x≠0)
variable (faces : ∀S : Finset (Fin 3),S.card<3→∀z : Word 3,Affine (F.face h S z))
include full faces in
theorem repeated_cube (z : Word 3) (i j k : Fin 3) (repeated : ¬(i≠j ∧ i≠k ∧ j≠k)) :
    thirdRatio h z (basis i) (basis j) (basis k)=1 := by
  have small : ({i,j,k} : Finset (Fin 3)).card<3 := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals try { norm_num at repeated }
    all_goals norm_num
  exact F.cube_of_affine_face h full z i j k (faces _ small z)

include full faces in
theorem cubic_ne_one (bad : ¬Affine h) : R.cubicRatio h≠1 := by
  intro equal
  apply bad
  apply F.affine_of_coordinate_cubes h full
  intro z i j k
  by_cases distinct : i≠j ∧ i≠k ∧ j≠k
  · rw [R.distinct_cube_ratio _ _ _ _ _ distinct,equal]
    split_ifs <;> simp
  · exact repeated_cube h full faces z i j k distinct

include full faces in
theorem core_affine (square : Affine (fun x=>h x^2)) (bad : ¬Affine h) :
    Affine (fun x=>A.phaseSeven x*h x) := by
  have hs := thirdTrivial_of_affine (fun x=>pow_ne_zero 2 (full x)) square
    (origin 3) (basis 0) (basis 1) (basis 2)
  rw [R.thirdRatio_square,R.origin_cube_ratio] at hs
  have negative : R.cubicRatio h= -1 := (sq_eq_one_iff.mp hs).resolve_left (cubic_ne_one h full faces bad)
  apply F.affine_of_coordinate_cubes _
    (fun x=>mul_ne_zero (A.twist_nonzero (A.codeSeven x)) (full x))
  intro z i j k
  rw [R.thirdRatio_mul]
  change thirdRatio A.phaseSeven z (basis i) (basis j) (basis k)*thirdRatio h z (basis i) (basis j) (basis k)=1
  rw [R.phaseSeven_cubes]
  by_cases distinct : i≠j ∧ i≠k ∧ j≠k
  · rw [ite_eq_left distinct,R.distinct_cube_ratio _ _ _ _ _ distinct,negative]
    split_ifs <;> norm_num
  · rw [ite_eq_right distinct,repeated_cube h full faces z i j k distinct,one_mul]

/-- The exact supported local twist counts agreeing one-positions in the
fourteen original ports. -/
def phase (a x : Word 3) : AlgebraicComplex :=
  ∏j : Fin 14,if embed a j && embed x j then zetaEight else 1

theorem embed_vector (x : Word 3) : embed x=
    ![x 0,x 1,x 2,x 1^^x 2,x 0^^x 2,x 0^^x 1,(x 0^^x 1)^^x 2,
      !(x 0),!(x 1),!(x 2),!(x 1^^x 2),!(x 0^^x 2),!(x 0^^x 1),!((x 0^^x 1)^^x 2)] := by
  funext i
  fin_cases i <;> rfl

theorem phase_formula (a x : Word 3) : phase a x= -(zetaEight^3)*A.phaseSeven (xor x a) := by
  have ae : a=![a 0,a 1,a 2] := by funext i;fin_cases i <;> rfl
  have xe : x=![x 0,x 1,x 2] := by funext i;fin_cases i <;> rfl
  rw [ae,xe]
  cases a 0 <;> cases a 1 <;> cases a 2 <;> cases x 0 <;> cases x 1 <;> cases x 2 <;>
    simp [phase,embed_vector,Fin.prod_univ_succ,A.phaseSeven_formula,AffinePhase.xor,AffinePhase.origin,pow_succ]
  all_goals ring_nf
  all_goals linear_combination zetaEight^3*zetaEight_pow_four

include full faces in
theorem phase_affine (square : Affine (fun x=>h x^2)) (bad : ¬Affine h) (a : Word 3) :
    Affine (fun x=>phase a x*h x) := by
  have hc := ((multiplier_affine a).mul (core_affine h full faces square bad)).scale (-(zetaEight^3))
  convert hc using 1
  funext x
  rw [phase_formula]
  dsimp only [multiplier,Pi.smul_apply,smul_eq_mul]
  have hs := phase_square x
  linear_combination (zetaEight^3)*A.phaseSeven (xor x a)*h x*hs

theorem local_twist (a : Word 3) :
    localTwist (embed a) (lift h)=lift (fun x=>phase a x*h x) := by
  funext z
  by_cases hz : z=embed (project z)
  · simp only [localTwist_apply,lift,NoXAffineEmbeddingLift.lift,ite_eq_left hz]
    rw [hz]
    simp only [project_embed,phase]
  · simp only [localTwist_apply,lift,NoXAffineEmbeddingLift.lift,ite_eq_right hz,mul_zero]

include full faces in
theorem local_of_nonAffine (square : Affine (fun x=>h x^2)) (bad : ¬Affine h) : LocalAffine (lift h) := by
  intro z supported
  have hz : z=embed (project z) := by
    by_contra neg
    exact supported (by simp [lift,NoXAffineEmbeddingLift.lift,neg])
  rw [hz,local_twist]
  exact affine_lift (phase_affine h full faces square bad _)

include full faces in
theorem affine_of_not_local (square : Affine (fun x=>h x^2)) (bad : ¬LocalAffine (lift h)) : Affine h := by
  by_contra negative
  exact bad (local_of_nonAffine h full faces square negative)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalOppositeSevenPhase
end
