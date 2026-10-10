import Holant.Proofs.Algorithms.CyclicBoundary.NonsquareIndex


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.ActualCards
open Holant.Projective.CyclicQuaternary Holant.Projective.CyclicPhasePencil
open Holant.Certificates.FourthRootOdd Holant.Certificates.TwelveLoops
open Holant.ReedMuller.CoefficientAtlas Holant.OpenNetworkComposition
open ZeroEndpointDressing CoordinateFactors ZeroEndpointRealization
noncomputable section

def pair (i : Fin 3) (side : Bool) : Fin 6 :=
  if side then CrossedTables.complementPair i else ⟨i.val,by omega⟩

theorem pair_word (i : Fin 3) (side a b u v : Bool) :
    insertPair (pair i side) a b ![u,v] = Holant.Projective.CyclicQuaternary.join i side a b u v := by
  funext j
  fin_cases i <;> fin_cases j <;> cases side <;>
    simp [pair,CrossedTables.complementPair,insertPair,portEquiv,portInverse,
      Holant.Projective.CyclicQuaternary.join]

def physical₂ (T : Kernel ℂ) : Signature ℂ 2 :=
  Signature.coordinateAction (fun _ => hadamard) (PhysicalAttachments.binary T)

def close (q : Signature ℂ 4) (p : Fin 6) : Signature ℂ 2 :=
  Signature.contract Signature.disequality (Tensor.reindex (portEquiv p).symm q)

theorem actual_close {F : SignatureFamily ℂ} (q : Signature ℂ 4) (p : Fin 6)
    (hq : Gadget.RealizesUpTo F .disequality q) :
    Gadget.RealizesUpTo F .disequality (close q p) :=
  realizesUpTo_contract F _
    (ProjectiveSubstitution.realizesUpTo_reindex F (portEquiv p).symm q hq) (by norm_num)

theorem dressed_contract (q : Signature ℂ 4) (i : Fin 3) (side : Bool) (s : ℂ) :
    Signature.contract ((2:ℂ) • TwoCopyKernels.diagonal 1 (-1))
      (Tensor.reindex (portEquiv (pair i side)).symm
        (dress q (internalPhases (pair i side) s 1))) =
      (2:ℂ) • PhysicalAttachments.binary
        (Holant.Projective.CyclicQuaternary.contraction q i side s) := by
  funext x
  have hx : x=![x 0,x 1] := by funext j; fin_cases j <;> rfl
  rw [hx]
  change (∑ a : Bool, ∑ b : Bool,
      (2*TwoCopyKernels.diagonal 1 (-1) a b)*
        dress q (internalPhases (pair i side) s 1) (insertPair (pair i side) a b ![x 0,x 1])) = _
  simp_rw [dress_insertPair,pair_word]
  simp [PhysicalAttachments.binary,Holant.Projective.CyclicQuaternary.contraction,
    TwoCopyKernels.diagonal,Holant.Projective.CyclicPhasePencil.diagonal]
  ring

theorem close_dressed_formula (q : Signature ℂ 4) (i : Fin 3) (side : Bool) (s : ℂ) :
    close (physical (dress q (internalPhases (pair i side) s 1))) (pair i side) =
      (2:ℂ) • physical₂ (Holant.Projective.CyclicQuaternary.contraction q i side s) := by
  unfold close physical
  rw [←coordinateAction_reindex,coordinateAction_contract,native_hadamard_edge,dressed_contract]
  funext x
  simp [physical₂,Signature.coordinateAction,Finset.mul_sum,mul_left_comm,mul_assoc]

theorem actual_contraction {F : SignatureFamily ℂ} {N : ℕ}
    (R : PhysicalAttachments.Representatives F N) (q : Signature ℂ 4)
    (hq : Gadget.RealizesUpTo F .disequality (physical q))
    (i : Fin 3) (side : Bool) (s : ℂ) (hs : s^N=1) :
    Gadget.RealizesUpTo F .disequality
      (physical₂ (Holant.Projective.CyclicQuaternary.contraction q i side s)) := by
  have hr := PhysicalAttachments.phase_dressing_upTo R q hq
    (internalPhases (pair i side) s 1) (internal_roots _ hs (one_pow N))
  have hc := actual_close _ (pair i side) hr
  rw [close_dressed_formula] at hc
  obtain ⟨c,hc0,hc⟩ := hc
  refine ⟨c*2,mul_ne_zero hc0 (by norm_num),?_⟩
  simpa only [Pi.smul_apply,smul_eq_mul,mul_assoc] using hc

theorem transpose_physical₂ (T : Kernel ℂ) :
    physical₂ (Kernel.transpose T) = Tensor.reindex (Equiv.swap (0:Fin 2) 1) (physical₂ T) := by
  unfold physical₂
  rw [←coordinateAction_reindex]
  congr 1

theorem actual_ordered {F : SignatureFamily ℂ} {N : ℕ}
    (R : PhysicalAttachments.Representatives F N) (q : Signature ℂ 4)
    (hq : Gadget.RealizesUpTo F .disequality (physical q))
    (i : Fin 3) (side order : Bool) (s : ℂ) (hs : s^N=1) :
    Gadget.RealizesUpTo F .disequality (physical₂ (orderedContraction q i side order s)) := by
  have h := actual_contraction R q hq i side s hs
  cases order
  · exact h
  · change Gadget.RealizesUpTo F .disequality
      (physical₂ (Kernel.transpose (Holant.Projective.CyclicQuaternary.contraction q i side s)))
    rw [transpose_physical₂]
    exact ProjectiveSubstitution.realizesUpTo_reindex F _ _ h

/-- Transfer in the fixed analytic coordinates, with the source's right Z.
This definition is not an additional edge tensor available to the algorithm. -/
def walshTransfer (B : Signature ℂ 2) : Kernel ℂ :=
  Kernel.mul (fun u v =>
    Signature.coordinateAction (fun _ => inverseHadamard) B ![u,v]) Z

theorem walshTransfer_physical₂ (T : Kernel ℂ) : walshTransfer (physical₂ T)=Kernel.mul T Z := by
  unfold walshTransfer physical₂
  rw [Signature.coordinateAction_cancel _ _ (fun _ => inverse_hadamard)]
  rfl

theorem walshTransfer_zero : walshTransfer 0=0 := by
  funext a b
  simp [walshTransfer,Signature.coordinateAction_zero,Kernel.mul]

structure OutsideCard (F : SignatureFamily ℂ) (N : ℕ) where
  signature : Signature ℂ 2
  actual : Gadget.RealizesUpTo F .disequality signature
  nonzero : signature ≠ 0
  outside : ¬IsPhase N (walshTransfer signature)

theorem failed_deck_actual {F : SignatureFamily ℂ} {N : ℕ}
    (R : PhysicalAttachments.Representatives F N) (q : Signature ℂ 4)
    (hq : Gadget.RealizesUpTo F .disequality (physical q))
    (hbad : ¬AllPhaseCards N q) : Nonempty (OutsideCard F N) := by
  classical
  unfold AllPhaseCards at hbad
  push_neg at hbad
  obtain ⟨i,side,order,s,hs,hn,hout⟩ := hbad
  refine ⟨⟨physical₂ (orderedContraction q i side order s),
    actual_ordered R q hq i side order s hs,?_,?_⟩⟩
  · intro hz
    have ht := congrArg walshTransfer hz
    rw [walshTransfer_physical₂,walshTransfer_zero] at ht
    exact hn ht
  · simpa only [walshTransfer_physical₂,transferCard] using hout

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.ActualCards
