import Holant.Proofs.Closure.ClosureSixPortGaugeContradiction
import Holant.Proofs.Closure.ClosureSixPortComplementary
import Holant.Proofs.Closure.ClosureSixPortBooleanGauge

/-! NEW UNVERIFIED internally chosen normalization coordinates for C/C.
The first actual C ruling chooses the residual order and all four flip tags. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant

variable {m : ℕ} {h : Signature ℂ 6} {e : Equiv.Perm (Fin 6)}

def ComplementarySector.normalOrder (D : ComplementarySector m h e false) : Equiv.Perm (Fin 6) :=
  (liftResidual (rulingPortsOrder D.ports)).trans e

def ComplementarySector.normalFlip (D : ComplementarySector m h e false) : Word 6 :=
  ![false,false,false,D.fixedParity,D.orientation,D.orientation^^D.parity]

def ComplementarySector.normalWord (D : ComplementarySector m h e false) (w : Word 6) : Word 6 :=
  gaugeWord D.normalOrder D.normalFlip w

open ComplementarySector

theorem normalOrder_first (D : ComplementarySector m h e false) : D.normalOrder 0=e 0 := by
  change e (liftResidual (rulingPortsOrder D.ports) ((finSumFinEquiv : (Fin 2 ⊕ Fin 4) ≃ Fin 6) (.inl (0 : Fin 2)))) = _
  convert congrArg e (liftResidual_left (rulingPortsOrder D.ports) 0) using 1 <;> rfl

theorem normalOrder_second (D : ComplementarySector m h e false) : D.normalOrder 1=e 1 := by
  change e (liftResidual (rulingPortsOrder D.ports) ((finSumFinEquiv : (Fin 2 ⊕ Fin 4) ≃ Fin 6) (.inl (1 : Fin 2)))) = _
  convert congrArg e (liftResidual_left (rulingPortsOrder D.ports) 1) using 1 <;> rfl

theorem normalOrder_residual (D : ComplementarySector m h e false) (i : Fin 4) :
    D.normalOrder ((rulingPortsOrder D.ports).symm i).succ.succ = e i.succ.succ := by
  change e (liftResidual (rulingPortsOrder D.ports) _) = _
  rw [liftResidual_right,Equiv.apply_symm_apply]

@[simp] theorem normalWord_first (D : ComplementarySector m h e false) (w : Word 6) :
    D.normalWord w (e 0) = w 0 := by
  rw [←normalOrder_first D]
  simp [normalWord,normalFlip]

@[simp] theorem normalWord_second (D : ComplementarySector m h e false) (w : Word 6) :
    D.normalWord w (e 1) = w 1 := by
  rw [←normalOrder_second D]
  simp [normalWord,normalFlip]

theorem normalWord_residual (D : ComplementarySector m h e false) (w : Word 6) (i : Fin 4) :
    residualSix e (D.normalWord w) i =
      (w ((rulingPortsOrder D.ports).symm i).succ.succ ^^
        D.normalFlip ((rulingPortsOrder D.ports).symm i).succ.succ) := by
  unfold residualSix
  rw [←normalOrder_residual D i]
  exact gaugeWord_apply_at _ _ _ _

@[simp] theorem rulingOrder_inverse_zero (ports : (Fin 2 × Bool) ≃ Fin 4) :
    (rulingPortsOrder ports).symm (ports (0,false))=0 := by
  rw [←rulingPorts_zero]
  exact Equiv.symm_apply_apply _ _
@[simp] theorem rulingOrder_inverse_one (ports : (Fin 2 × Bool) ≃ Fin 4) :
    (rulingPortsOrder ports).symm (ports (0,true))=1 := by
  rw [←rulingPorts_one]
  exact Equiv.symm_apply_apply _ _
@[simp] theorem rulingOrder_inverse_two (ports : (Fin 2 × Bool) ≃ Fin 4) :
    (rulingPortsOrder ports).symm (ports (1,false))=2 := by
  rw [←rulingPorts_two]
  exact Equiv.symm_apply_apply _ _
@[simp] theorem rulingOrder_inverse_three (ports : (Fin 2 × Bool) ≃ Fin 4) :
    (rulingPortsOrder ports).symm (ports (1,true))=3 := by
  rw [←rulingPorts_three]
  exact Equiv.symm_apply_apply _ _

/-- The first C sector normalizes to the four literal first-flat words. -/
theorem normal_first_sector_support (D : ComplementarySector m h e false) (w : Word 6)
    (even : w 1=w 0) :
    h (D.normalWord w) ≠ 0 ↔ w ∈ firstFlatSupport := by
  have hp : (D.normalWord w (e 0) ^^ D.normalWord w (e 1))=false := by
    rw [normalWord_first,normalWord_second,even,Bool.xor_self]
  rw [D.word_support _ hp,firstFlat_support_iff]
  simp only [normalWord_residual,rulingOrder_inverse_zero,rulingOrder_inverse_one,
    rulingOrder_inverse_two,rulingOrder_inverse_three]
  have r0 : (0 : Fin 4).succ.succ = (2 : Fin 6) := rfl
  have r1 : (1 : Fin 4).succ.succ = (3 : Fin 6) := rfl
  have r2 : (2 : Fin 4).succ.succ = (4 : Fin 6) := rfl
  have r3 : (3 : Fin 4).succ.succ = (5 : Fin 6) := rfl
  simp only [r0,r1,r2,r3,normalWord_first]
  have flip2 : D.normalFlip 2 = false := rfl
  have flip3 : D.normalFlip 3 = D.fixedParity := rfl
  have flip4 : D.normalFlip 4 = D.orientation := rfl
  have flip5 : D.normalFlip 5 = (D.orientation^^D.parity) := rfl
  rw [flip2,flip3,flip4,flip5,Bool.xor_false]
  change (((w 3 ^^ D.fixedParity) = (w 2 ^^ D.fixedParity)) ∧
    ((w 4 ^^ D.orientation) = (D.orientation ^^ w 0)) ∧
    ((w 5 ^^ (D.orientation^^D.parity)) = ((D.orientation^^w 0)^^D.parity))) ↔
      w 1=w 0 ∧ w 3=w 2 ∧ w 4=w 0 ∧ w 5=w 0
  have fixed := fixed_coordinate_gauge false (w 2) (w 3) false D.fixedParity D.fixedParity
  have varying := varying_coordinate_gauge false (w 4) (w 5) D.orientation
    (D.orientation^^D.parity) D.orientation (w 0) D.parity
  cases hp0 : D.fixedParity <;> cases hp1 : D.parity <;> cases ho : D.orientation <;> simp_all

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
