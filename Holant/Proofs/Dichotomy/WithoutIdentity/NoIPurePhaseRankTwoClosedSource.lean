import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankTwoScalar
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankTwoCore
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankThreeSource

/-! Lightweight rank-two correction with an exact original signed-port
presentation. Only genuine Affine faces and support geometry are used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoClosedSource
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace R
export NoIPurePhaseRankTwoScalar (rho rho_nonzero)
end R
namespace C
export NoIPurePhaseIncidenceCore.C (codeThree)
end C
namespace P
export NoIPurePhaseRecipeFactor (Port word incidence)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {n : ℕ}

def SameMod4 (f : Signature AlgebraicComplex n) : Prop:=
  ∀x y,f x≠0→f y≠0→weight x%4=weight y%4

theorem cross_weight (p : Fin n→P.Port 3) :
    (weight (P.word p (C.codeThree ![false,false])) : ℤ)+
      weight (P.word p (C.codeThree ![true,true]))-
      weight (P.word p (C.codeThree ![false,true]))-
      weight (P.word p (C.codeThree ![true,false]))= -2*P.incidence p 2 := by
  unfold weight P.incidence
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases h:p i with
  | inl b=>cases b <;>simp [P.word,C.codeThree,h]
  | inr t=>
    rcases t with ⟨j,s⟩
    fin_cases j <;>cases s <;>simp [P.word,C.codeThree,h]

variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)

/-- The physical row uses the same root-sixteen phase as the rank-three
case. The encoding equality retains every signed original character. -/
theorem source (bad : ¬Affine f)
    (faces : ∀i : Fin 2,∀z : Word 2,Affine (minor D {i} z))
    (p : Fin n→P.Port 3) (encoding : ∀x,P.word p (C.codeThree x)=D.encode x)
    (same : SameMod4 f) (residue : P.incidence p 2%4=2) :
    Affine (NoIPurePhaseRankThreeSource.twist R.rho f) := by
  have fourth:=NoIPurePhaseRankTwoSource.faces_fourth D faces
  have reducedBad:=NoIPureClosedMinimal.nonAffine_reduced D bad
  have cross:(weight (D.encode ![false,false])+weight (D.encode ![true,true]))%8=
      (weight (D.encode ![false,true])+weight (D.encode ![true,false])+4)%8:=by
    have h:=cross_weight p
    simp only [encoding] at h
    omega
  have reduced:Affine (fun x=>R.rho^(weight (D.encode x))*D.reduced x):=
    NoIPurePhaseRankTwoScalar.affine (fun x=>weight (D.encode x)) D.reduced
      D.reduced_full fourth reducedBad
      (fun x=>same _ _ (D.supported x) (D.supported _)) cross
  let E : SystematicSupport (NoIPurePhaseRankThreeSource.twist R.rho f) 2:={
    ports:=D.ports
    injective:=D.injective
    encode:=D.encode
    affine:=D.affine
    free:=D.free
    supported x:=mul_ne_zero (pow_ne_zero _ R.rho_nonzero) (D.supported x)
    covers x hx:=D.covers x (mul_ne_zero_iff.mp hx).2 }
  obtain ⟨S,hS⟩:=NoIPureClosedMinimal.support_system f
    (NoIPureClosedMinimal.chart_closed D) (NoIPureClosedMinimal.chart_nonzero D)
  apply E.affine_of_reduced S ?_ reduced
  intro x
  change S.Holds x↔R.rho^(weight x)*f x≠0
  simpa only [mul_ne_zero_iff,and_iff_right (pow_ne_zero _ R.rho_nonzero)] using hS x

theorem all_three (bad : ¬Affine f)
    (faces : ∀i : Fin 2,∀z : Word 2,Affine (minor D {i} z))
    (p : Fin n→P.Port 3) (encoding : ∀x,P.word p (C.codeThree x)=D.encode x)
    (same : SameMod4 f) (residue : ∀j,P.incidence p j%4=2) :
    Affine (NoIPurePhaseRankThreeSource.twist R.rho f) :=
  source D bad faces p encoding same (residue 2)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoClosedSource
end
