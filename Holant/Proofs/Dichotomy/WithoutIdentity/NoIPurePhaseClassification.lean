import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankThreeCases
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseBlockAnchor
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankOneLegal

/-! Shared four-phase selection for one unchanged original coefficient row.
Minimum witnesses are pure pinnings of that row; a single fixed anchor
neutralizes later incompatible witnesses. The selected phase is shared over
the whole row, so applying this theorem to the actual whole-family tensor
provides one phase for every original label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseClassification
open Holant Holant.Tractable
open NoIPurePhaseBlock
open NoIPurePhaseLegalAffine (LegalAffine)
namespace U
export NoIPureClosedUniformMinimal (twist UniformPinWitness exists_minimal_uniform)
end U
namespace R
export NoIPurePhaseRankTwoScalar (rho rho_nonzero rho_sixteen)
end R
namespace C
export NoIPurePhaseIncidenceCore.C (codeSeven)
end C
namespace M
export NoIPurePhaseLiftBlock (TwoCase)
export NoIPurePhaseRankThreeCases (OddCase)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {n : ℕ}
variable (f : Signature K n)
variable (closed : NoIPureClosedMinimal.C.Closed (fun x=>(f x : AlgebraicComplex)))
variable (uniform : NoIPureChargeTwoFamily.UniformFour (fun x=>(f x : AlgebraicComplex)))
variable (legal : LegalAffine (fun x=>(f x : AlgebraicComplex)))

include closed uniform legal in
theorem minimum_case (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1)
    (bad : ¬Affine (U.twist r (fun x=>(f x : AlgebraicComplex)))) :
    Nonempty (M.TwoCase r (fun x=>(f x : AlgebraicComplex))) ∨
      Nonempty (M.OddCase r (fun x=>(f x : AlgebraicComplex))) := by
  have nonzero : f≠0 := by
    intro hz
    apply bad
    have he : U.twist r (fun x=>(f x : AlgebraicComplex))=0 := by
      funext x
      simp [NoIPureClosedUniformMinimal.twist,hz]
    rw [he]
    exact affine_zero n
  obtain ⟨rank,lo,hi,W,minimal⟩:=U.exists_minimal_uniform r rn f closed nonzero bad
  interval_cases rank
  · exact False.elim (NoIPurePhaseRankOneLegal.pin_impossible f uniform legal r rn root W)
  · exact Or.inl ⟨NoIPurePhaseLiftBlock.produce W minimal uniform legal rn root⟩
  · exact NoIPurePhaseRankThreeCases.produce f uniform legal r rn root W minimal

include closed uniform legal in
/-- Every failed phase supplies a literal original-row block whose corrected
code pullback is bad and whose seven signed charges have one common value. -/
theorem bad_test (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1)
    (bad : ¬Affine (U.twist r (fun x=>(f x : AlgebraicComplex)))) :
    ∃B : Block n 7,∃t : ZMod 4,(∀j,(NoIPurePhaseBlock.charge B j : ZMod 4)=t) ∧
      ¬Affine (fun x : Fin 3→Bool=>phase r (fun z=>(f z : AlgebraicComplex)) B (C.codeSeven x)) := by
  rcases minimum_case f closed uniform legal r rn root bad with two|odd
  · obtain ⟨D⟩:=two
    exact ⟨D.block,2,D.charge2,D.bad⟩
  · obtain ⟨D⟩:=odd
    exact ⟨D.block,D.a,D.charge,D.bad⟩

include closed uniform legal in
/-- Once an odd anchor has been chosen, every later witness uses that exact
phase and anchor. The conclusion concerns the entire original row. -/
theorem affine_of_odd_anchor (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1)
    (A : Block n 7) (a : ZMod 4) (odd : a=1 ∨ a=3)
    (count : ∀j,(NoIPurePhaseBlock.charge A j : ZMod 4)=a)
    (good : Affine (phase r (fun x=>(f x : AlgebraicComplex)) A))
    (full : ∀x : Fin 3→Bool,value (fun z=>(f z : AlgebraicComplex)) A (C.codeSeven x)≠0) :
    Affine (U.twist r (fun x=>(f x : AlgebraicComplex))) := by
  by_contra bad
  obtain ⟨B,t,test,obstruction⟩:=bad_test f closed uniform legal r rn root bad
  exact NoIPurePhaseBlockAnchor.odd_excludes (fun x=>(f x : AlgebraicComplex)) legal
    r rn root A B a t odd count test good full obstruction

theorem root_pow (k : ℕ) : (R.rho^k)^16=1 := by
  calc
    (R.rho^k)^16=(R.rho^16)^k := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    _=1 := by rw [R.rho_sixteen,one_pow]

include closed uniform legal in
/-- One of four fixed phases works for the entire original row. No phase is
chosen separately for its minimum witnesses or its individual factors. -/
theorem classified : ∃k : Fin 4,
    Affine (fun x=>(R.rho^k.val)^(weight x)*(f x : AlgebraicComplex)) := by
  classical
  let F : Signature AlgebraicComplex n:=fun x=>(f x : AlgebraicComplex)
  by_cases ordinary : Affine F
  · exact ⟨0,by simpa using ordinary⟩
  have bad : ¬Affine (U.twist 1 F) := by
    intro h
    apply ordinary
    change Affine (fun x => (1 : AlgebraicComplex) ^ weight x * F x) at h
    simpa only [one_pow,one_mul] using h
  rcases minimum_case f closed uniform legal 1 one_ne_zero (by simp) bad with two|odd
  · obtain ⟨A⟩:=two
    have anchor : Affine (phase R.rho F A.block) := by simpa only [one_mul] using A.affine
    by_cases good : Affine (U.twist R.rho F)
    · refine ⟨1,?_⟩
      change Affine (fun x=>R.rho ^ weight x * F x) at good
      simpa only [Fin.val_one,pow_one] using good
    rcases minimum_case f closed uniform legal R.rho R.rho_nonzero R.rho_sixteen good with other|odd
    · obtain ⟨B⟩:=other
      exact False.elim (NoIPurePhaseBlockAnchor.two_excludes F legal R.rho R.rho_nonzero
        R.rho_sixteen A.block B.block A.charge2 B.charge2 anchor A.full B.bad)
    · obtain ⟨B⟩:=odd
      have he : R.rho*R.rho^2=R.rho^3 := by ring
      have anchor3 : Affine (phase (R.rho^3) F B.block) := by simpa only [he] using B.affine
      have result:=affine_of_odd_anchor f closed uniform legal (R.rho^3)
        (pow_ne_zero _ R.rho_nonzero) (root_pow 3) B.block B.a B.odd B.charge anchor3 B.full
      exact ⟨3,result⟩
  · obtain ⟨A⟩:=odd
    have anchor2 : Affine (phase (R.rho^2) F A.block) := by simpa only [one_mul] using A.affine
    have result:=affine_of_odd_anchor f closed uniform legal (R.rho^2)
      (pow_ne_zero _ R.rho_nonzero) (root_pow 2) A.block A.a A.odd A.charge anchor2 A.full
    exact ⟨2,result⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseClassification
end
