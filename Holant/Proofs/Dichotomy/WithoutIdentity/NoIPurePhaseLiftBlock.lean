import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseBlockTransform
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankTwoLift
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankTwoCubic
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseLiftBlockPins

/-! Three copies of an actual original-row block lift the three binary
characters to all seven ternary characters.  Products and phase constants
are exact; no compressed row is introduced as a physical resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseLiftBlock
open Holant Holant.Tractable
open scoped BigOperators
namespace R
export NoIPurePhaseBlock
  (Block value charge phase single append flatten pinLift rename
    value_single charge_single phase_single value_append charge_append phase_append
    value_flatten charge_flatten phase_flatten value_pinLift charge_pinLift phase_pinLift
    value_rename charge_rename phase_rename word_affine)
end R
namespace L
export NoIPurePhaseRankTwoLift (map logical code_value)
end L
namespace C
export NoIPurePhaseIncidenceCore.C (codeThree codeSeven)
export NoIPurePhaseRankTwoCubic (upgrade upgrade_full not_affine)
end C
namespace U
export NoIPureClosedUniformMinimal (twist twistChart UniformPinWitness)
end U
namespace P
export NoIPurePhaseSmallPorts (two two_value)
end P
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option Elab.async false
variable {n : ℕ}

def lift (B : R.Block n 3) : R.Block n 7 :=
  R.flatten (fun i : Fin 3 => R.rename B (L.map i))

theorem lift_count (B : R.Block n 3) : (lift B).count = 3*B.count := by
  simp only [lift, NoIPurePhaseBlock.flatten, NoIPurePhaseBlock.rename, Fin.sum_univ_three]
  omega

theorem value_code (f : Signature AlgebraicComplex n) (B : R.Block n 3)
    (x : Fin 3 → Bool) :
    R.value f (lift B) (C.codeSeven x) =
      C.upgrade (fun y => R.value f B (C.codeThree y)) x := by
  simp only [lift, R.value_flatten, R.value_rename, L.code_value,
    Fin.prod_univ_three, L.logical, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, C.upgrade]
  rfl

theorem phase_code (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : R.Block n 3) (x : Fin 3 → Bool) :
    R.phase r f (lift B) (C.codeSeven x) =
      C.upgrade (fun y => R.phase r f B (C.codeThree y)) x := by
  simp only [lift, R.phase_flatten, R.phase_rename, L.code_value,
    Fin.prod_univ_three, L.logical, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, C.upgrade]
  rfl

theorem charge_two (B : R.Block n 3)
    (two : ∀j, (R.charge B j : ZMod 4)=2) (j : Fin 7) :
    (R.charge (lift B) j : ZMod 4)=2 := by
  simp only [lift, R.charge_flatten, R.charge_rename, Int.cast_sum,
    Int.cast_ite, Int.cast_zero]
  simp_rw [two]
  revert j
  decide

theorem full_code (f : Signature AlgebraicComplex n) (B : R.Block n 3)
    (full : ∀x : Fin 2 → Bool, R.value f B (C.codeThree x) ≠ 0) :
    ∀x : Fin 3 → Bool, R.value f (lift B) (C.codeSeven x) ≠ 0 := by
  intro x
  rw [value_code]
  exact C.upgrade_full _ full x

theorem rename_affine (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : R.Block n 3) (e : Fin 3 → Fin 7) (good : Affine (R.phase r f B)) :
    Affine (R.phase r f (R.rename B e)) := by
  have hf : TwoTranslate.IsAffineMap (fun z : Fin 7 → Bool => fun j => z (e j)) := by
    intro x y
    funext j
    simp [AffinePhase.xor, AffinePhase.origin]
  convert good.precompose _ hf using 1
  funext z
  exact R.phase_rename r f B e z

theorem affine (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : R.Block n 3) (good : Affine (R.phase r f B)) :
    Affine (R.phase r f (lift B)) := by
  have h := ((rename_affine r f B (L.map 0) good).mul
    (rename_affine r f B (L.map 1) good)).mul
      (rename_affine r f B (L.map 2) good)
  convert h using 1
  funext z
  simp only [lift, R.phase_flatten, Fin.prod_univ_three]

theorem bad_code (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (B : R.Block n 3)
    (full : ∀x : Fin 2 → Bool, R.phase r f B (C.codeThree x) ≠ 0)
    (fourth : Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification.CommonFourth
      (fun x => R.phase r f B (C.codeThree x)))
    (bad : ¬Affine (fun x : Fin 2 → Bool => R.phase r f B (C.codeThree x))) :
    ¬Affine (fun x : Fin 3 → Bool => R.phase r f (lift B) (C.codeSeven x)) := by
  simpa only [phase_code] using C.not_affine _ full fourth bad

def fromPins {m : ℕ} (p : Fin n → Bool ⊕ Fin m)
    (q : Fin m → NoIPurePhaseRecipeFactor.Port 3) : R.Block n 7 :=
  R.pinLift p (lift (R.single q))

theorem fromPins_count {m : ℕ} (p : Fin n → Bool ⊕ Fin m)
    (q : Fin m → NoIPurePhaseRecipeFactor.Port 3) : (fromPins p q).count = 3 := by
  change (lift (R.single q)).count = 3
  rw [lift_count]
  rfl

theorem fromPins_value {m : ℕ} (f : Signature AlgebraicComplex n)
    (p : Fin n → Bool ⊕ Fin m) (q : Fin m → NoIPurePhaseRecipeFactor.Port 3)
    (x : Fin 3 → Bool) :
    R.value f (fromPins p q) (C.codeSeven x) =
      C.upgrade (fun y => f (NoIPurePhasePinCompose.substitute p
        (NoIPurePhaseRecipeFactor.word q (C.codeThree y)))) x := by
  rw [fromPins, R.value_pinLift, value_code]
  simp only [R.value_single]

/-- The three pinned phase constants remain as the displayed scalar. -/
theorem fromPins_phase {m : ℕ} (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (p : Fin n → Bool ⊕ Fin m) (pure : NoIPurePhasePinCompose.PurePins p)
    (q : Fin m → NoIPurePhaseRecipeFactor.Port 3) (x : Fin 3 → Bool) :
    R.phase r f (fromPins p q) (C.codeSeven x) =
      (r ^ NoIPurePhasePinCompose.fixedWeight p)^3 *
        C.upgrade (fun y => r ^ weight (NoIPurePhaseRecipeFactor.word q (C.codeThree y)) *
          f (NoIPurePhasePinCompose.substitute p
            (NoIPurePhaseRecipeFactor.word q (C.codeThree y)))) x := by
  rw [fromPins, R.phase_pinLift r f p pure, phase_code, lift_count]
  simp only [show (R.single q).count = 1 from rfl, mul_one, R.phase_single]

/-- A genuine three-copy original-row block supplies both a bad current
phase test and a full corrected Affine anchor at the same next phase. -/
structure TwoCase (r : AlgebraicComplex) (f : Signature AlgebraicComplex n) where
  block : R.Block n 7
  charge2 : ∀j, (R.charge block j : ZMod 4)=2
  full : ∀x : Fin 3 → Bool, R.value f block (C.codeSeven x) ≠ 0
  bad : ¬Affine (fun x : Fin 3 → Bool => R.phase r f block (C.codeSeven x))
  affine : Affine (R.phase (r*NoIPurePhaseRankTwoScalar.rho) f block)

/-- The minimum-rank witness is an actual pure pinning of the coefficient
field row.  The resulting three-copy block uses that original row alone. -/
def produce {K : IntermediateField ℚ AlgebraicComplex} {f : Signature K n}
    {r : AlgebraicComplex} (W : U.UniformPinWitness r f 2)
    (minimal : ∀S : Finset (Fin 2), S.card < 2 → ∀z : Fin 2 → Bool,
      Affine (U.twist r (OrdinaryNegativeSparseRankDescent.minor W.chart S z)))
    (uniform : NoIPureChargeTwoFamily.UniformFour (fun x => (f x : AlgebraicComplex)))
    (legal : NoIPurePhaseLegalAffine.LegalAffine (fun x => (f x : AlgebraicComplex)))
    (rn : r ≠ 0) (root : r^16=1) : TwoCase r (fun x => (f x : AlgebraicComplex)) := by
  let F : Signature AlgebraicComplex n := fun x => (f x : AlgebraicComplex)
  let g := OrdinaryNegativeSparseMinimalRank.row f W.pins
  let base := R.single (P.two W.chart)
  let lifted := lift base
  let original := fromPins W.pins (P.two W.chart)
  have up : NoIPureChargeTwoFamily.UniformFour g :=
    NoIPurePhasePinCompose.uniform_four F uniform W.pins W.pure
  have lp : NoIPurePhaseLegalAffine.LegalAffine g :=
    NoIPurePhaseLegalPins.pin F legal W.pins W.pure
  have two := NoIPurePhaseLiftBlockPins.all_three_two W.chart up lp r rn root W.bad
  have anchor := NoIPurePhaseLiftBlockPins.corrected_anchor W.chart up lp r rn root W.bad minimal
  let E := U.twistChart r rn W.chart
  have faces (i : Fin 2) (z : Fin 2 → Bool) :
      Affine (OrdinaryNegativeSparseRankDescent.minor E {i} z) :=
    (NoIPureClosedUniformMinimal.twist_minor_affine_iff r rn W.chart {i} z).mpr
      (minimal {i} (by simp) z)
  have equal : (fun x : Fin 2 → Bool => R.phase r g base (C.codeThree x)) = E.reduced := by
    funext x
    simp only [base, R.phase_single, P.two_value]
    rfl
  have badLift : ¬Affine (fun x : Fin 3 → Bool => R.phase r g lifted (C.codeSeven x)) := by
    apply bad_code r g base
    · intro x
      rw [show R.phase r g base (C.codeThree x) = E.reduced x from congrFun equal x]
      exact E.reduced_full x
    · rw [equal]
      exact NoIPurePhaseRankTwoSource.faces_fourth E faces
    · rw [equal]
      exact NoIPureClosedMinimal.nonAffine_reduced E W.bad
  refine ⟨original, ?_, ?_, ?_, ?_⟩
  · intro j
    change (R.charge (R.pinLift W.pins lifted) j : ZMod 4) = 2
    rw [R.charge_pinLift W.pins W.pure]
    apply charge_two base
    simpa only [base, R.charge_single] using two
  · intro x
    change R.value F (R.pinLift W.pins lifted) (C.codeSeven x) ≠ 0
    rw [R.value_pinLift]
    apply full_code g base
    intro y
    simpa only [base, R.value_single, P.two_value] using W.chart.supported y
  · intro good
    apply badLift
    have hn := NoIPurePhaseBlock.pin_scalar_nonzero r rn W.pins lifted
    convert good.scale ((r ^ NoIPurePhasePinCompose.fixedWeight W.pins) ^ lifted.count)⁻¹ using 1
    funext x
    change R.phase r g lifted (C.codeSeven x) =
      ((r ^ NoIPurePhasePinCompose.fixedWeight W.pins) ^ lifted.count)⁻¹ *
        R.phase r F (R.pinLift W.pins lifted) (C.codeSeven x)
    rw [R.phase_pinLift r F W.pins W.pure lifted]
    change R.phase r g lifted (C.codeSeven x) =
      ((r ^ NoIPurePhasePinCompose.fixedWeight W.pins) ^ lifted.count)⁻¹ *
        ((r ^ NoIPurePhasePinCompose.fixedWeight W.pins) ^ lifted.count *
          R.phase r g lifted (C.codeSeven x))
    rw [←mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · have baseGood : Affine (R.phase (r*NoIPurePhaseRankTwoScalar.rho) g base) := by
      have h := anchor.precompose (NoIPurePhaseRecipeFactor.word (P.two W.chart))
        (R.word_affine (P.two W.chart))
      convert h using 1
      funext z
      exact R.phase_single (r*NoIPurePhaseRankTwoScalar.rho) g (P.two W.chart) z
    have liftedGood := affine (r*NoIPurePhaseRankTwoScalar.rho) g base baseGood
    convert liftedGood.scale
      (((r*NoIPurePhaseRankTwoScalar.rho) ^ NoIPurePhasePinCompose.fixedWeight W.pins) ^ lifted.count)
      using 1
    funext x
    exact R.phase_pinLift (r*NoIPurePhaseRankTwoScalar.rho) F W.pins W.pure lifted x


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseLiftBlock
end
