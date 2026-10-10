import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMLabels

/-! Exact real model and original matching coordinates of a signed translated
Pauli fiber. The phase components of the shifts factor into a boundary sign. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMFiber
open Holant
namespace H
export GlobalCloseCompletionKleinHigherNonaffine (Label E EOver Matching)
end H
namespace F
export GlobalCloseCompletionKleinHigherNonaffine.Fiber (tensor)
end F
namespace C
export GlobalCloseCompletionKleinEightRMLabels (label labelEquiv phasePack shiftPack one map_E shifted_E weight_phase shift_bits)
end C
namespace D
export GlobalCloseCompletionKleinEightRMData (sign weight shift toggle source order mask word)
end D
namespace T
export GlobalCloseCompletionC2BitTranslateActual (translate)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def ports : (Fin 4×Bool)≃Fin 8 :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv

def basisOrder (M : H.Matching (Fin 8) 4) : Equiv.Perm (Fin 8) := M.ports.symm.trans ports

def realFiber (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool) (shifts : Fin 4→H.Label) : Signature ℝ 8 :=
  fun x=>∑k : Fin 4,(D.sign (phase (C.label k)):ℝ)*
    ∏e : Fin 4,H.EOver (0:ℝ) (C.label k+shifts e) (x (M.ports (e,false))) (x (M.ports (e,true)))

def body (phase : H.Label→Bool) (shifts : Fin 4→H.Label) : Signature ℝ 8 :=
  fun x=>∑k : Fin 4,(D.sign (phase (C.label k)):ℝ)*
    ∏e : Fin 4,H.EOver (0:ℝ) (C.label k+shifts e)
      (x (finProdFinEquiv (e,(0:Fin 2)))) (x (finProdFinEquiv (e,(1:Fin 2))))

theorem real_E (a : H.Label) (u v : Bool) : (H.EOver (K:=ℝ) (0:ℝ) a u v:ℂ)=H.E a u v := by
  exact C.map_E Complex.ofRealHom a u v

theorem complex_fiber (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool)
    (shifts : Fin 4→H.Label) (scale : ℂ) :
    F.tensor M (fun a=>scale*(if phase a then -1 else 1)) (fun a e=>a+shifts e)=
      fun x=>scale*(realFiber M phase shifts x:ℂ) := by
  funext x
  unfold F.tensor GlobalCloseCompletionKleinHigherNonaffine.Matching.tensor
  rw [←Equiv.sum_comp C.labelEquiv
    (fun a=>scale*(if phase a then (-1:ℂ) else 1)*
      ∏e : Fin 4,H.E (a+shifts e) (x (M.ports (e,false))) (x (M.ports (e,true))))]
  simp only [realFiber,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod,real_E,Finset.mul_sum,C.labelEquiv]
  apply Finset.sum_congr rfl
  intro k _
  change scale*(if phase (C.label k) then (-1:ℂ) else 1)*_=
    scale*(((D.sign (phase (C.label k)):ℝ):ℂ)*_)
  cases h : phase (C.label k) <;> simp [D.sign,h,mul_assoc]

theorem reindexed (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool) (shifts : Fin 4→H.Label) :
    Tensor.reindex (basisOrder M) (realFiber M phase shifts)=body phase shifts := by
  funext x
  simp only [Tensor.reindex,realFiber,body,basisOrder,Equiv.trans_apply,
    Equiv.symm_apply_apply,ports,Equiv.prodCongr_apply,Equiv.refl_apply]
  try rfl

theorem body_factor (phase : H.Label→Bool) (phase0 : phase 0=false)
    (shifts : Fin 4→H.Label) (shifts0 : shifts 0=0) (x : Fin 8→Bool) :
    body phase shifts x=(∏e : Fin 4,(D.sign (C.one (shifts e).1 && x (finProdFinEquiv (e,(0:Fin 2)))):ℝ))*
      (D.source (C.phasePack phase) (C.shiftPack shifts) x:ℝ) := by
  simp only [body,C.shifted_E,Finset.prod_mul_distrib,D.source,Int.cast_sum,Int.cast_mul,Int.cast_prod]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [C.weight_phase phase phase0]
  simp_rw [C.shift_bits shifts shifts0]
  ring

theorem charted (M : H.Matching (Fin 8) 4) (phase : H.Label→Bool) (shifts : Fin 4→H.Label)
    (x : Fin 8→Bool) :
    T.translate (Tensor.reindex ((basisOrder M).trans (D.order (C.phasePack phase)))
      (realFiber M phase shifts)) (D.mask (C.phasePack phase) (C.shiftPack shifts)) x=
      body phase shifts (D.word (C.phasePack phase) (C.shiftPack shifts) x) := by
  exact congrFun (reindexed M phase shifts) (D.word (C.phasePack phase) (C.shiftPack shifts) x)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMFiber
end
