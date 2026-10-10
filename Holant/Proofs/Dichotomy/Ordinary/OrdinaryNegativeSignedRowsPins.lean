import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockPurePins
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsSource

/-! Precompose signed row ports with a genuine pure pinning of an original
row. Every surviving original coordinate appears exactly once, so bundle
sizes are unchanged. The physical compiler uses the unchanged original row;
a pinned minor is never presumed to be an available target label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsPins
open Holant Holant.Algebraic
open OrdinaryNegativeSignedPortsCore
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseMinimalRank (PurePins)
end P
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace S
export OrdinaryNegativeSignedRowsSource (block block_value)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {N n m r : ℕ}
variable (pins : Fin N→Bool ⊕ Fin n) (hp : P.PurePins pins)

def signedCompose (p : Fin n→Port m) : Fin N→Port m :=
  fun i=>Sum.elim Sum.inl p (pins i)

theorem word_compose (p : Fin n→Port m) (z : Fin m→Bool) :
    word (signedCompose pins p) z=T.substitute pins (word p z) := by
  funext i
  cases h : pins i <;> simp [signedCompose,word,T.substitute,h]

include hp in
/-- Counting through a pure pinning retains each surviving summand once. -/
theorem sum_pure {A : Type*} [AddCommMonoid A] (f : Fin n→A) :
    (∑i : Fin N,Sum.elim (fun _=>0) f (pins i))=∑j,f j := by
  calc
    _=∑i : Fin N,∑j : Fin n,if pins i=Sum.inr j then f j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases pins i <;> simp
    _=∑j : Fin n,∑i : Fin N,if pins i=Sum.inr j then f j else 0 := Finset.sum_comm
    _=∑j,f j := by
      apply Finset.sum_congr rfl
      intro j _
      obtain ⟨i,hi,unique⟩ := hp j
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro q _ hq
        have he : pins q≠Sum.inr j := fun h=>hq (unique q h)
        simp [he]
      · simp

include hp in
theorem bundleSize_compose (p : Fin n→Port m) (j : Fin m) :
    I.bundleSize (signedCompose pins p) j=I.bundleSize p j := by
  unfold I.bundleSize
  calc
    _=∑i : Fin N,Sum.elim (fun _=>0)
      (fun q=>match p q with | .inl _=>0 | .inr (k,_)=>if k=j then 1 else 0) (pins i) := by
        apply Finset.sum_congr rfl
        intro i _
        cases h : pins i with
        | inl v => simp [signedCompose,h]
        | inr q =>
          simp only [signedCompose,h,Sum.elim_inr]
          rfl
    _=_ := sum_pure pins hp _

def lifted (p : Fin r→Fin n→Port m) : Fin r→Fin N→Port m :=
  fun i=>signedCompose pins (p i)

include hp in
theorem lifted_even (p : Fin r→Fin n→Port m) (he : ∀j,Even (∑i,I.bundleSize (p i) j)) :
    ∀j,Even (∑i,I.bundleSize (lifted pins p i) j) := by
  intro j
  simpa only [lifted,bundleSize_compose pins hp] using he j

variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (labels : Fin 4→Fin s)
variable (f : Signature K N)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨arity N i.val,table f i⟩)
variable (p : Fin r→Fin n→Port m) (he : ∀j,Even (∑i,I.bundleSize (p i) j))

def block := S.block H labels f literal (lifted pins p) (lifted_even pins hp p he)

theorem block_value (z : Fin m→Bool) :
    (block pins hp H labels f literal p he).signature H z=
      ∏i,f (T.substitute pins (word (p i) z)) := by
  rw [block,S.block_value]
  apply Finset.prod_congr rfl
  intro i _
  rw [lifted,word_compose]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsPins
end
