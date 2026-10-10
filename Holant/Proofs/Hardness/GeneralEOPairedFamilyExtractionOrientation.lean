import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyFieldClosed

/-! Signed compressed literals are realized by reversing the relevant
oriented pair directions. The original signature, original port order and
support covering remain literal; no disequality signature is adjoined. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionOrientation
open Holant Holant.Tractable
namespace C
export GeneralEOPairedCSPCycles (Covers Compatible compress)
end C
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

variable {n : ℕ} (p : OrientedPerfectPairing n) (signs : Fin p.count → Bool)

def flipPorts : Equiv.Perm (Fin p.count×Bool) where
  toFun q := (q.1,Bool.xor (signs q.1) q.2)
  invFun q := (q.1,Bool.xor (signs q.1) q.2)
  left_inv := by rintro ⟨i,b⟩; dsimp; simp
  right_inv := by rintro ⟨i,b⟩; dsimp; simp

def pairing : OrientedPerfectPairing n where
  count := p.count
  ports := (flipPorts p signs).trans p.ports

def xorWord (z : Fin p.count → Bool) : Fin p.count → Bool :=
  fun i => Bool.xor (signs i) (z i)

theorem ports_value (i : Fin p.count) (b : Bool) :
    (pairing p signs).ports (i,b)=p.ports (i,Bool.xor (signs i) b) := rfl

theorem word_value (z : Fin p.count → Bool) :
    (pairing p signs).word z=p.word (xorWord p signs z) := by
  funext k
  obtain ⟨⟨i,b⟩,rfl⟩ := p.ports.surjective k
  simp only [OrientedPerfectPairing.word,pairing,Equiv.symm_trans_apply,
    Equiv.symm_apply_apply,flipPorts,xorWord]
  change (if Bool.xor (signs i) b then !(z i) else z i)=
    (if b then !(Bool.xor (signs i) (z i)) else Bool.xor (signs i) (z i))
  cases signs i <;> cases b <;> cases z i <;> rfl

theorem compatible_iff (x : Fin n → Bool) :
    C.Compatible (pairing p signs) x ↔ C.Compatible p x := by
  unfold C.Compatible Holant.LocalDrafts.Tractability.EOEvaluation.PairLift.Compatible
  apply forall_congr'
  intro i
  rw [ports_value,ports_value]
  cases signs i
  · rfl
  · exact ne_comm

variable {K : Type*} [Zero K] (f : Signature K n)

theorem covers (hf : C.Covers p f) : C.Covers (pairing p signs) f := by
  intro x hx
  exact (compatible_iff p signs x).mpr (hf x hx)

omit [Zero K] in
theorem compressed_value (z : Fin p.count → Bool) :
    C.compress (pairing p signs) f z=C.compress p f (xorWord p signs z) := by
  unfold C.compress
  rw [word_value]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionOrientation
