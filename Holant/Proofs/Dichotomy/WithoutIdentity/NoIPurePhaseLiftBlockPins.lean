import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseSmallPorts
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseLegalPins
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankTwoClosedSource

/-! The rank-two source before its three-copy lift.  Every port is an
original-coordinate signed substitution and every pinned phase is retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseLiftBlockPins
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open NoIPurePhaseRecipeFactor (Port word incidence)
open NoIPurePhaseLegalAffine (LegalAffine)
namespace U
export NoIPureClosedUniformMinimal (twist twistChart UniformPinWitness)
end U
namespace P
export NoIPurePhaseSmallPorts (two two_value)
export NoIPurePhasePinCompose (compose substitute word_compose fixedWeight weight_substitute)
end P
namespace C
export NoIPurePhaseIncidenceCore.C (codeThree)
end C
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option Elab.async false
variable {n : ℕ} {f : Signature AlgebraicComplex n}

theorem codeThree_affine : TwoTranslate.IsAffineMap C.codeThree := by
  unfold TwoTranslate.IsAffineMap
  decide

theorem corrected_of_reduced (D : SystematicSupport f 2)
    (r : AlgebraicComplex) (rn : r ≠ 0)
    (good : Affine (fun x => U.twist r f (D.encode x))) : Affine (U.twist r f) := by
  let E := U.twistChart r rn D
  obtain ⟨S,hS⟩ := NoIPureClosedMinimal.support_system f
    (NoIPureClosedMinimal.chart_closed D) (NoIPureClosedMinimal.chart_nonzero D)
  apply E.affine_of_reduced S ?_ good
  intro x
  exact (hS x).trans (NoIPureClosedUniformMinimal.twist_support r rn f x).symm

theorem all_three_two (D : SystematicSupport f 2)
    (uniform : NoIPureChargeTwoFamily.UniformFour f) (legal : LegalAffine f)
    (r : AlgebraicComplex) (rn : r ≠ 0) (root : r^16=1)
    (bad : ¬Affine (U.twist r f)) :
    ∀j, (incidence (P.two D) j : ZMod 4)=2 := by
  have zeroCode : C.codeThree (![false,false] : Fin 2 → Bool) = (fun _ => false) := by
    funext j
    fin_cases j <;> rfl
  have same (x : Fin 2 → Bool) :
      weight (word (P.two D) (C.codeThree x)) % 4 =
        weight (word (P.two D) (fun _ => false)) % 4 := by
    rw [←zeroCode, P.two_value, P.two_value]
    exact uniform _ _ (D.supported _) (D.supported _)
  rcases NoIPurePhaseIncidencePorts.rank_two (P.two D) same with zero | two
  · exfalso
    apply bad
    have hz (j : Fin 3) : incidence (P.two D) j % 4 = 0 :=
      Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (zero j))
    have good := (NoIPurePhaseLegalAffine.single_corrected f legal r rn root
      (P.two D) hz).precompose C.codeThree codeThree_affine
    apply corrected_of_reduced D r rn
    simpa only [P.two_value, U.twist] using good
  · exact two

theorem twist_mul (a b : AlgebraicComplex) (f : Signature AlgebraicComplex n) :
    U.twist a (U.twist b f) = U.twist (a*b) f := by
  funext x
  simp only [U.twist, mul_pow]
  ring

theorem corrected_anchor (D : SystematicSupport f 2)
    (uniform : NoIPureChargeTwoFamily.UniformFour f) (legal : LegalAffine f)
    (r : AlgebraicComplex) (rn : r ≠ 0) (root : r^16=1)
    (bad : ¬Affine (U.twist r f))
    (minimal : ∀S : Finset (Fin 2), S.card < 2 → ∀z : Fin 2 → Bool,
      Affine (U.twist r (minor D S z))) :
    Affine (U.twist (r*NoIPurePhaseRankTwoScalar.rho) f) := by
  let E := U.twistChart r rn D
  have faces (i : Fin 2) (z : Fin 2 → Bool) : Affine (minor E {i} z) :=
    (NoIPureClosedUniformMinimal.twist_minor_affine_iff r rn D {i} z).mpr
      (minimal {i} (by simp) z)
  have same : NoIPurePhaseRankTwoClosedSource.SameMod4 (U.twist r f) := by
    intro x y hx hy
    exact uniform x y (mul_ne_zero_iff.mp hx).2 (mul_ne_zero_iff.mp hy).2
  have two := all_three_two D uniform legal r rn root bad
  have residues (j : Fin 3) : incidence (P.two D) j % 4 = 2 := by
    have hz := (ZMod.intCast_eq_intCast_iff' (incidence (P.two D) j) 2 4).mp (two j)
    norm_num at hz
    exact hz
  have good := NoIPurePhaseRankTwoClosedSource.all_three E bad faces
    (P.two D) (P.two_value D) same residues
  change Affine (U.twist NoIPurePhaseRankTwoScalar.rho (U.twist r f)) at good
  rw [twist_mul, mul_comm NoIPurePhaseRankTwoScalar.rho r] at good
  exact good


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseLiftBlockPins
end
