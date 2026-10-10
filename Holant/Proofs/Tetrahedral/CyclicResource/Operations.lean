import Holant.Proofs.Tetrahedral.CyclicResource.Networks


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant Holant.Certificates.FourthRootOdd Holant.Certificates.TwelveLoops
open Holant.LocalDrafts.MainChain.CyclicBoundary
open ZeroEndpointDressing PhysicalAttachments TwoCopyKernels TwoCopyTransport
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def attachOrder (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := ![if i=0 then 0 else 2,if i=1 then 0 else 3,
    if i=2 then 0 else 4,if i=3 then 0 else 5,⟨i.val+2,by omega⟩,1]
  invFun := ![i.castLE (by decide),5,if i=0 then 4 else 0,
    if i=1 then 4 else 1,if i=2 then 4 else 2,if i=3 then 4 else 3]
  left_inv := by intro j; fin_cases i <;> fin_cases j <;> decide
  right_inv := by intro j; fin_cases i <;> fin_cases j <;> decide

variable {ι : Type*} {q : Signature ℂ 4} {B : ι → Kernel ℂ}

def Circuit.attach (C : Circuit q B 4) (i : Fin 4) (r : ι) : Circuit q B 4 :=
  .contract (.reorder (.tensor C (.auxiliary r)) (attachOrder i))

theorem Circuit.attach_calls (C : Circuit q B 4) (i : Fin 4) (r : ι) :
    (C.attach i r).calls = C.calls := by simp [attach,calls]

theorem Circuit.attach_denote (C : Circuit q B 4) (i : Fin 4) (r : ι) :
    (C.attach i r).network.denote = PhysicalAttachments.attach C.network.denote i (B r) := by
  rw [attach,network,Network.denote_contract,network,reorderNetwork_denote,
    network,Network.denote_tensor,network,singleVertexNetwork_denote,attach_eq_splice]
  funext x
  have hx : x = ![x 0,x 1,x 2,x 3] := by ext j; fin_cases j <;> rfl
  rw [hx]
  have hw (w : Fin 6 → Bool) : (fun j : Fin 4 => w ((attachOrder i) (Fin.castAdd 2 j))) =
      ![w ((attachOrder i) 0),w ((attachOrder i) 1),w ((attachOrder i) 2),w ((attachOrder i) 3)] := by
    funext j; fin_cases j <;> rfl
  simp only [Signature.contract, Signature.tensor_apply, Tensor.reindex, hw]
  fin_cases i <;>
    simp [attachOrder,Signature.contract,Signature.tensor_apply,Tensor.reindex,
      Holant.OpenNetworkComposition.spliceTensor,PhysicalAttachments.binary,
      update_word,Signature.disequality] <;> ring

def Circuit.attachAll (C : Circuit q B 4) (r : Fin 4 → ι) : Circuit q B 4 :=
  (((C.attach 0 (r 0)).attach 1 (r 1)).attach 2 (r 2)).attach 3 (r 3)

theorem Circuit.attachAll_calls (C : Circuit q B 4) (r : Fin 4 → ι) :
    (C.attachAll r).calls = C.calls := by simp only [attachAll,attach_calls]

theorem Circuit.attachAll_denote (C : Circuit q B 4) (r : Fin 4 → ι) :
    (C.attachAll r).network.denote = PhysicalAttachments.attachAll C.network.denote (fun i => B (r i)) := by
  simp only [attachAll,attach_denote]
  exact four_attachments C.network.denote (fun i => B (r i))

def Certificate.dress {F : SignatureFamily ℂ} {N k : ℕ}
    (R : Representatives F N) {q f : Signature ℂ 4}
    (W : Certificate q R.matrix (physical f) k)
    (s : Fin 4 → ℂ) (hs : ∀ i, (s i)^N=1) :
    Certificate q R.matrix (physical (ZeroEndpointDressing.dress f s)) k := by
  let r : Fin 4 → {s : ℂ // s^N=1} := fun i => ⟨s i,hs i⟩
  let d : ℂ := 2^4 * ∏ i, R.scalar (r i)
  have hd : d ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => R.scalar_ne_zero (r i)))
  refine ⟨W.circuit.attachAll r,(W.circuit.attachAll_calls r).trans W.calls_eq,
    W.scalar*d,mul_ne_zero W.scalar_ne_zero hd,?_⟩
  rw [Circuit.attachAll_denote,W.equation]
  change Signature.coordinateAction _ (W.scalar • physical f) = _
  rw [action_scale]
  change W.scalar • PhysicalAttachments.attachAll (physical f) (fun i => R.matrix (r i)) = _
  rw [physical_attachment_formula f (fun i => R.matrix (r i)) s
    (fun i => R.scalar (r i)) (fun i => R.action (r i)),smul_smul]

def Circuit.join (L R : Circuit q B 4) (p : Fin 6) : Circuit q B 4 :=
  .contract (n:=4) (.contract (n:=6) (.reorder (.tensor (m:=4) (n:=4) L R) (copyEquiv p).symm))

theorem Circuit.join_calls (L R : Circuit q B 4) (p : Fin 6) :
    (L.join R p).calls = L.calls + R.calls := rfl

theorem Circuit.join_denote (L R : Circuit q B 4) (p : Fin 6) :
    (L.join R p).network.denote =
      contraction L.network.denote R.network.denote p Signature.disequality Signature.disequality := by
  rw [join,network,Network.denote_contract,network,Network.denote_contract,
    network,reorderNetwork_denote,network,Network.denote_tensor,←contraction_as_contracts]

def Certificate.join {k l : ℕ} {f g : Signature ℂ 4}
    (L : Certificate q B f k) (R : Certificate q B g l) (p : Fin 6) :
    Certificate q B (contraction f g p Signature.disequality Signature.disequality) (k+l) := by
  refine ⟨L.circuit.join R.circuit p,by rw [Circuit.join_calls,L.calls_eq,R.calls_eq],
    L.scalar*R.scalar,mul_ne_zero L.scalar_ne_zero R.scalar_ne_zero,?_⟩
  rw [Circuit.join_denote,L.equation,R.equation]
  simpa only [one_smul,one_mul] using
    contraction_scales L.scalar R.scalar 1 1 f g p Signature.disequality Signature.disequality

def Certificate.close {k} {f : Signature ℂ 4} (W : Certificate q B f k) (p : Fin 6) :
    Certificate q B (ActualCards.close f p) k := by
  refine ⟨.contract (.reorder W.circuit (portEquiv p).symm),W.calls_eq,
    W.scalar,W.scalar_ne_zero,?_⟩
  rw [Circuit.network,Network.denote_contract,Circuit.network,reorderNetwork_denote,W.equation]
  funext x
  simp [ActualCards.close,Tensor.reindex,Signature.contract,Finset.mul_sum,mul_left_comm,mul_assoc]
  ring

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
