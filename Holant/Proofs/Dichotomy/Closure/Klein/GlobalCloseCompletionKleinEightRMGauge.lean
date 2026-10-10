import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMFiber
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMValues
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinPhaseActual

/-! The translated equal-square eight-port fiber is normalized to literal
2·RM8 by one port permutation, native bit translations and actual linear
Pauli signs. The original matching and every label shift are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMGauge
open Holant
namespace H
export GlobalCloseCompletionKleinHigherNonaffine (Label Matching)
end H
namespace F
export GlobalCloseCompletionKleinEightRMFiber (basisOrder realFiber body body_factor charted)
end F
namespace C
export GlobalCloseCompletionKleinEightRMLabels (phasePack shiftPack one)
end C
namespace D
export GlobalCloseCompletionKleinEightRMData (sign correction source order mask word rm reverse)
end D
namespace A
export GlobalCloseCompletionKleinPhaseActual (phase)
end A
namespace T
export GlobalCloseCompletionC2BitTranslateActual (translate)
end T
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def tailSign (shifts : Fin 4→H.Label) (x : Fin 8→Bool) : ℤ :=
  ∏e : Fin 4,D.sign (C.one (shifts e).1 && x (finProdFinEquiv (e,(0:Fin 2))))
def character (phase : H.Label→Bool) (shifts : Fin 4→H.Label) (x : Fin 8→Bool) : ℤ :=
  D.correction (C.phasePack phase) x*tailSign shifts x

def phaseMask (phase : H.Label→Bool) (shifts : Fin 4→H.Label) : Fin 8→Bool :=
  ![(C.phasePack phase).val.testBit 0,(C.phasePack phase).val.testBit 0,
    C.one (shifts 1).1,false,C.one (shifts 2).1,false,C.one (shifts 3).1,false]
def phaseSet (phase : H.Label→Bool) (shifts : Fin 4→H.Label) : Finset (Fin 8) :=
  Finset.univ.filter (fun i=>phaseMask phase shifts i=true)

theorem correction_split (s : Fin 8) (x : Fin 8→Bool) :
    D.correction s x=D.sign (s.val.testBit 0 && x 0)*D.sign (s.val.testBit 0 && x 1) := by
  unfold D.correction
  cases s.val.testBit 0 <;> cases x 0 <;> cases x 1 <;> rfl

theorem sign_square (b : Bool) : D.sign b^2=1 := by cases b <;> norm_num [D.sign]

theorem character_square (phase : H.Label→Bool) (shifts : Fin 4→H.Label) (x : Fin 8→Bool) :
    character phase shifts x^2=1 := by
  rw [character,mul_pow]
  simp only [D.correction,tailSign,←Finset.prod_pow,sign_square,Finset.prod_const_one,one_mul]

theorem tail_word (shifts : Fin 4→H.Label) (zero : shifts 0=0) (s b : Fin 8) (x : Fin 8→Bool) :
    tailSign shifts (D.word s b x)=tailSign shifts x := by
  cases hr : D.reverse s <;>
    simp [tailSign,Fin.prod_univ_succ,zero,C.one,D.sign,D.word,D.order,hr,D.mask,
      finProdFinEquiv,Equiv.swap_apply_def]

variable {K : Type*} [Field K]

theorem phase_value (phase : H.Label→Bool) (shifts : Fin 4→H.Label) (zero : shifts 0=0)
    (f : Signature K 8) (x : Fin 8→Bool) :
    A.phase (phaseSet phase shifts) f x=(character phase shifts x:K)*f x := by
  have factor (i : Fin 8) :
      (if phaseMask phase shifts i=true then (if x i then (-1:K) else 1) else 1)=
        (D.sign (phaseMask phase shifts i && x i):K) := by
    cases phaseMask phase shifts i <;> cases x i <;> norm_num [D.sign]
  have product : (∏i : Fin 8,D.sign (phaseMask phase shifts i && x i))=character phase shifts x := by
    simp only [character,correction_split,tailSign,phaseMask,Fin.prod_univ_succ,
      Fin.prod_univ_zero,mul_one,zero,C.one]
    norm_num [D.sign,finProdFinEquiv]
  simp only [A.phase,phaseSet,Finset.prod_filter]
  simp_rw [factor]
  rw [←Int.cast_prod,product]

theorem rm_cast (x : Fin 8→Bool) : (D.rm x:ℝ)=R.rm x := by
  rw [GlobalCloseCompletionKleinH6RMBell.rm_check]
  unfold D.rm
  split_ifs <;> norm_num

theorem chart_value (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool) (phase0 : phase 0=false)
    (shifts : Fin 4→H.Label) (shifts0 : shifts 0=0) (x : Fin 8→Bool) :
    T.translate (Tensor.reindex ((F.basisOrder M).trans (D.order (C.phasePack phase)))
      (F.realFiber M phase shifts)) (D.mask (C.phasePack phase) (C.shiftPack shifts)) x=
      2*(character phase shifts x:ℝ)*R.rm x := by
  rw [F.charted,F.body_factor phase phase0 shifts shifts0,GlobalCloseCompletionKleinEightRMValues.value]
  have boundary : (∏e : Fin 4,(D.sign (C.one (shifts e).1 &&
      D.word (C.phasePack phase) (C.shiftPack shifts) x (finProdFinEquiv (e,(0:Fin 2)))):ℝ))=
      (tailSign shifts x:ℝ) := by
    rw [←Int.cast_prod]
    exact congrArg (fun z : ℤ=>(z:ℝ)) (tail_word shifts shifts0 _ _ x)
  rw [boundary]
  simp only [Int.cast_mul,Int.cast_ofNat,rm_cast,character]
  ring

theorem normalized (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool) (phase0 : phase 0=false)
    (shifts : Fin 4→H.Label) (shifts0 : shifts 0=0) :
    A.phase (phaseSet phase shifts)
      (T.translate (Tensor.reindex ((F.basisOrder M).trans (D.order (C.phasePack phase)))
        (F.realFiber M phase shifts)) (D.mask (C.phasePack phase) (C.shiftPack shifts)))= (2:ℝ) • (R.rm (K:=ℝ)) := by
  funext x
  rw [phase_value phase shifts shifts0,chart_value M phase phase0 shifts shifts0]
  have square : (character phase shifts x:ℝ)^2=1 := by exact_mod_cast character_square phase shifts x
  simp only [Pi.smul_apply,smul_eq_mul]
  change (character phase shifts x:ℝ)*(2*(character phase shifts x:ℝ)*R.rm x)=2*R.rm x
  calc
    _=2*(character phase shifts x:ℝ)^2*R.rm x := by ring
    _=2*R.rm x := by rw [square,mul_one]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMGauge
end
