import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixReconstruction
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixPackedSafety
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncodingValues

/-! The sixteen finite cross-card probes are the literal Bell contractions
of four boundary permutations of the reconstructed real six-port source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixCrossCoordinates
open Holant
namespace D
export GlobalCloseCompletionKleinSixFiniteData (fill card line)
end D
namespace F
export GlobalCloseCompletionKleinSixFiniteForms (tensor index6)
end F
namespace W
export GlobalCloseCompletionKleinGramCertificate (word pauli)
end W
namespace S
export GlobalCloseCompletionKleinRMPhaseSupport (word4)
end S
namespace B
export GlobalCloseCompletionKleinSixBellNorm (card matrix)
end B
namespace N
export GlobalCloseCompletionKleinGramNorm (rows)
end N
namespace C
export GlobalCloseCompletionKleinSixBellCoordinates (Normal)
end C
namespace Rec
export GlobalCloseCompletionKleinSixReconstruction (form phasePack)
end Rec
namespace P
export GlobalCloseCompletionKleinSixPacked (safe)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def orderData : Fin 4→Fin 6→Fin 6 :=
  ![![0,2,1,3,4,5],![0,2,3,1,4,5],![0,2,3,4,1,5],![0,2,3,4,5,1]]
def inverseData : Fin 4→Fin 6→Fin 6 :=
  ![![0,2,1,3,4,5],![0,3,1,2,4,5],![0,4,1,2,3,5],![0,5,1,2,3,4]]
theorem left_inverse : ∀j i,inverseData j (orderData j i)=i := by decide +kernel
theorem right_inverse : ∀j i,orderData j (inverseData j i)=i := by decide +kernel
def order (j : Fin 4) : Equiv.Perm (Fin 6) :=
  ⟨orderData j,inverseData j,left_inverse j,right_inverse j⟩

theorem fill_correct : ∀(j : Fin 4) (x : Fin 16) (t : Fin 4),
    F.index6 (fun i=>(Fin.addCases (m:=2) (n:=4) (W.word t) (S.word4 x) : Fin 6→Bool) (order j i))=
      D.fill j x t := by decide +kernel

theorem matrix_cast (k t : Fin 4) :
    B.matrix k t=(W.pauli k (W.word t 0) (W.word t 1):ℝ) := by
  fin_cases k <;> fin_cases t <;> norm_num [B.matrix,W.word,W.pauli,GlobalCloseCompletionKleinH6RMBell.E,GlobalCloseCompletionKleinH6RMBell.bell]

theorem finite_card (a b c : Fin 48) (s : Fin 8) (j k : Fin 4) (x : Fin 16) :
    B.card (Tensor.reindex (order j) (F.tensor (K:=ℝ) a b c s)) k (S.word4 x)=
      (D.card a b c s j k x:ℝ) := by
  simp only [B.card,N.rows,Tensor.reindex,F.tensor,fill_correct,D.card,Int.cast_sum,
    Int.cast_mul,matrix_cast]

theorem card_scale (f : Signature ℝ 6) (d : ℝ) (j k : Fin 4) (x : Fin 16) :
    B.card (Tensor.reindex (order j) (d • f)) k (S.word4 x)=
      d*B.card (Tensor.reindex (order j) f) k (S.word4 x) := by
  simp only [B.card,N.rows,Tensor.reindex,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem safe (f : Signature ℝ 6) (R : C.Normal f) (anchor : R.label 0=0)
    (j : Fin 4) (T : C.Normal (Tensor.reindex (order j) f)) (k : Fin 4) :
    P.safe (D.card (R.label 1) (R.label 2) (R.label 3) (Rec.phasePack R.phase) j k)=true := by
  let d : ℝ:=R.scale/2
  have hd : d≠0 := div_ne_zero R.scale_nonzero (by norm_num)
  have point (x : Fin 16) :
      (D.card (R.label 1) (R.label 2) (R.label 3) (Rec.phasePack R.phase) j k x:ℝ)=
        (T.scale*(GlobalCloseCompletionKleinSixMatchingCoordinates.sign (T.phase k):ℝ)/d)*
          (D.line (T.label k) x:ℝ) := by
    have eqCard := congrArg (fun g : Signature ℝ 6=>B.card (Tensor.reindex (order j) g) k (S.word4 x))
      (Rec.form f R anchor)
    rw [card_scale,finite_card] at eqCard
    have h := eqCard.symm.trans (T.value k x)
    change d*_=_ at h
    apply (mul_left_cancel₀ hd)
    calc
      _=T.scale*(GlobalCloseCompletionKleinSixMatchingCoordinates.sign (T.phase k):ℝ)*(D.line (T.label k) x:ℝ) := h
      _=d*((T.scale*(GlobalCloseCompletionKleinSixMatchingCoordinates.sign (T.phase k):ℝ)/d)*(D.line (T.label k) x:ℝ)) := by field_simp [hd]
  exact GlobalCloseCompletionKleinSixPackedSafety.safe_of_coordinates _
    (GlobalCloseCompletionKleinSixPackedSafety.card_bounds _ _ _ _ j k) (T.label k) _ point


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixCrossCoordinates
end
