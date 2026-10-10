import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseBlockWitness
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseLiftBlock
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankThreeOdd
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseLegalPins

/-! Actual minimum-rank ternary witnesses either cancel through their own
proper faces, or give one normalized physical anchor for the next common
phase. Both the current bad phase and the corrected Affine phase are kept. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankThreeCases
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open NoIPurePhaseRecipeFactor (Port word incidence)
open NoIPurePhaseLegalAffine (LegalAffine)
open NoIPurePhaseBlock
open NoIPurePhaseBlockWitness
namespace U
export NoIPureClosedUniformMinimal (twist twistChart UniformPinWitness)
end U
namespace P
export NoIPurePhaseSmallPorts (three three_value linearWord_pin linearWord_affine)
end P
namespace C
export NoIPurePhaseIncidenceCore.C (codeSeven)
export NoIPurePhaseIncidenceRegularization (pattern translated cases_of_pattern)
end C
namespace I
export NoIPurePhaseIncidenceWeight (residue)
end I
namespace R
export NoIPurePhaseRankTwoScalar (rho rho_nonzero rho_sixteen)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option Elab.async false
variable {n : ℕ}

structure OddCase (r : AlgebraicComplex) (f : Signature AlgebraicComplex n) where
  block : Block n 7
  a : ZMod 4
  odd : a=1 ∨ a=3
  charge : ∀j,(NoIPurePhaseBlock.charge block j : ZMod 4)=a
  full : ∀x : Fin 3→Bool,value f block (C.codeSeven x)≠0
  bad : ¬Affine (fun x : Fin 3→Bool=>phase r f block (C.codeSeven x))
  affine : Affine (phase (r*R.rho^2) f block)

theorem odd_of_translation (d : ℤ) (b : Bool) (a : ZMod 4)
    (odd : a=1 ∨ a=3) (eqn : (if b then -(d : ZMod 4) else (d : ZMod 4))=a) :
    d%2=1 := by
  have changeSign : ∀z : ZMod 4,∀s : Bool,
      ((if s then -z else z)=1 ∨ (if s then -z else z)=3)→z=1 ∨ z=3 := by decide
  have hz : (d : ZMod 4)=1 ∨ (d : ZMod 4)=3 :=
    changeSign _ b (odd.elim (fun h=>Or.inl (eqn.trans h)) (fun h=>Or.inr (eqn.trans h)))
  rcases hz with hz|hz
  · have hd: d%4=1 := by
      have h:=(ZMod.intCast_eq_intCast_iff' d 1 4).mp hz
      norm_num at h
      exact h
    omega
  · have hd: d%4=3 := by
      have h:=(ZMod.intCast_eq_intCast_iff' d 3 4).mp hz
      norm_num at h
      exact h
    omega

variable {K : IntermediateField ℚ AlgebraicComplex} (f : Signature K n)
variable (uniform : NoIPureChargeTwoFamily.UniformFour (fun x=>(f x : AlgebraicComplex)))
variable (legal : LegalAffine (fun x=>(f x : AlgebraicComplex)))
variable (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1)
variable (W : U.UniformPinWitness r f 3)
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,
  Affine (U.twist r (minor W.chart S z)))

include uniform legal rn root minimal in
theorem produce : Nonempty (NoIPurePhaseLiftBlock.TwoCase r (fun x=>(f x : AlgebraicComplex))) ∨
    Nonempty (OddCase r (fun x=>(f x : AlgebraicComplex))) := by
  let F : Signature AlgebraicComplex n:=fun x=>(f x : AlgebraicComplex)
  let g:=OrdinaryNegativeSparseMinimalRank.row f W.pins
  let p:=P.three W.chart
  let B:=pinBlock W.pins p
  let E:=U.twistChart r rn W.chart
  have lp : LegalAffine g:=NoIPurePhaseLegalPins.pin F legal W.pins W.pure
  have up : NoIPureChargeTwoFamily.UniformFour g:=
    NoIPurePhasePinCompose.uniform_four F uniform W.pins W.pure
  have encoding (x : Fin 3→Bool) : word p (C.codeSeven x)=W.chart.encode x:=P.three_value W.chart x
  have full (x : Fin 3→Bool) : g (word p (C.codeSeven x))≠0 := by
    rw [encoding]
    exact W.chart.supported x
  have reducedBad : ¬Affine (fun x : Fin 3→Bool=>U.twist r g (word p (C.codeSeven x))) := by
    have h:=NoIPureClosedMinimal.nonAffine_reduced E W.bad
    change ¬Affine (fun x => U.twist r g (W.chart.encode x)) at h
    simpa only [encoding] using h
  have blockFull (x : Fin 3→Bool) : value F B (C.codeSeven x)≠0 := by
    rw [pin_value]
    exact full x
  have blockBad : ¬Affine (fun x : Fin 3→Bool=>phase r F B (C.codeSeven x)) :=
    pin_bad r rn F W.pins W.pure p C.codeSeven reducedBad
  have minE : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (minor E S z) := by
    intro S hS z
    exact (NoIPureClosedUniformMinimal.twist_minor_affine_iff r rn W.chart S z).mpr (minimal S hS z)
  have zeroCode : C.codeSeven (fun _ : Fin 3=>false)=(fun _=>false) := by decide
  have same (x : Fin 3→Bool) : weight (word p (C.codeSeven x))%4=weight (word p (fun _=>false))%4 := by
    rw [←zeroCode,encoding,encoding]
    exact up _ _ (W.chart.supported _) (W.chart.supported _)
  obtain ⟨t,u,kernel⟩:=NoIPurePhaseIncidencePorts.rank_three p same
  rcases C.cases_of_pattern (I.residue p) t u kernel with regular|two|odd
  · obtain ⟨q,corrects⟩:=regular
    exfalso
    apply NoIPurePhaseIncidenceRecipe.product_bad r rn root g p q corrects full reducedBad
      (fun i=>?_) (lp 7 3 (NoIPurePhaseIncidencePorts.rows p q)
        (NoIPurePhaseIncidencePorts.rows_zero p q corrects))
    have h:=W.affine_of_fixed_coordinate rn minimal
      (NoIPurePhaseIncidencePorts.P.linearWord (q i)) (P.linearWord_affine (q i))
      (q i).axis false (P.linearWord_pin (q i))
    simpa only [encoding, NoIPurePhaseAnchorRecipe.corrected, U.twist] using h
  · have residues (j : Fin 7) : incidence p j%4=2 := by
      have h:=(ZMod.intCast_eq_intCast_iff' (incidence p j) 2 4).mp (two j)
      norm_num at h
      exact h
    have good:=NoIPurePhaseRankThreeSource.source E minE W.bad p encoding residues
    change Affine (U.twist R.rho (U.twist r g)) at good
    rw [NoIPurePhaseLiftBlockPins.twist_mul,mul_comm R.rho r] at good
    left
    refine ⟨⟨B,?_,blockFull,blockBad,pin_affine (r*R.rho) F W.pins W.pure p good⟩⟩
    intro j
    rw [pin_charge W.pins W.pure]
    exact two j
  · obtain ⟨v,hv⟩:=odd
    obtain ⟨a,ha,normalized⟩ : ∃a : ZMod 4,(a=1 ∨ a=3) ∧ ∀j,C.translated (I.residue p) v j=a := by
      rcases hv with h|h
      · exact ⟨1,Or.inl rfl,h⟩
      · exact ⟨3,Or.inr rfl,h⟩
    have residues (j : Fin 7) : incidence p j%2=1 :=
      odd_of_translation _ _ a ha (normalized j)
    have good:=NoIPurePhaseRankThreeOdd.source E minE W.bad p encoding residues
    change Affine (U.twist (R.rho^2) (U.twist r g)) at good
    rw [NoIPurePhaseLiftBlockPins.twist_mul,mul_comm (R.rho^2) r] at good
    have anchor : Affine (phase (r*R.rho^2) F B):=pin_affine _ F W.pins W.pure p good
    right
    refine ⟨⟨translate B (C.codeSeven v),a,ha,?_,?_,?_,?_⟩⟩
    · intro j
      rw [charge_translate,pin_charge W.pins W.pure]
      simpa only [Int.cast_ite,Int.cast_neg,I.residue,C.translated] using normalized j
    · exact translate_full_code F B v blockFull
    · exact fun h=>blockBad ((phase_translate_code_affine_iff r F B v).mp h)
    · exact translate_affine (r*R.rho^2) F B (C.codeSeven v) anchor

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankThreeCases
end
