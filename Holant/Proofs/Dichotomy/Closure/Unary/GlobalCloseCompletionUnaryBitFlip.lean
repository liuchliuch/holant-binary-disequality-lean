import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryFactor

/-! Semantic coordinate flips preserve actual tensor decompositions and
primality. The mask is used only to prove identities at another coefficient
pivot; no flipped signature is asserted to be an available physical gate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBitFlip
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] {n : ℕ}

def word (mask x : Fin n→Bool) : Fin n→Bool := fun i=>Bool.xor (x i) (mask i)
def value (mask : Fin n→Bool) (f : Signature K n) : Signature K n := fun x=>f (word mask x)

@[simp] theorem word_twice (mask x : Fin n→Bool) : word mask (word mask x)=x := by
  funext i
  simp [word]

@[simp] theorem value_twice (mask : Fin n→Bool) (f : Signature K n) : value mask (value mask f)=f := by
  funext x
  simp only [value,word_twice]

@[simp] theorem word_zero (mask : Fin n→Bool) : word mask (fun _=>false)=mask := by
  funext i
  simp [word]

@[simp] theorem value_zero (mask : Fin n→Bool) : value mask (0 : Signature K n)=0 := rfl

def decomposition (D : TensorDecomposition K n) (mask : Fin n→Bool) : TensorDecomposition K n where
  count := D.count
  arity := D.arity
  factor v := value (fun i=>mask (D.ports ⟨v,i⟩)) (D.factor v)
  ports := D.ports
  scale := D.scale

theorem decomposition_value (D : TensorDecomposition K n) (mask : Fin n→Bool) :
    (decomposition D mask).value=value mask D.value := rfl

theorem tensorClosure (mask : Fin n→Bool) (f : Signature K n)
    (small : Signature.TensorClosure (fun k (_ : Signature K k)=>k≤2) f) :
    Signature.TensorClosure (fun k (_ : Signature K k)=>k≤2) (value mask f) := by
  obtain ⟨D,small,rfl⟩ := small
  exact ⟨decomposition D mask,small,rfl⟩

theorem tensorClosure_iff (mask : Fin n→Bool) (f : Signature K n) :
    Signature.TensorClosure (fun k (_ : Signature K k)=>k≤2) (value mask f) ↔
      Signature.TensorClosure (fun k (_ : Signature K k)=>k≤2) f := by
  constructor
  · intro h
    have h' := tensorClosure mask (value mask f) h
    rwa [value_twice] at h'
  · exact tensorClosure mask f

def split {f a b : AnySignature K} (S : ProperSplit f a b) (mask : Fin f.1→Bool) :
    ProperSplit ⟨f.1,value mask f.2⟩
      ⟨a.1,value (fun i=>mask (S.ports (.inl i))) a.2⟩
      ⟨b.1,value (fun i=>mask (S.ports (.inr i))) b.2⟩ where
  left_pos := S.left_pos
  right_pos := S.right_pos
  ports := S.ports
  scale := S.scale
  equation := by
    funext x
    exact congrFun S.equation (word mask x)

theorem prime (mask : Fin n→Bool) (f : Signature K n)
    (hf : Prime (⟨n,f⟩ : AnySignature K)) : Prime (⟨n,value mask f⟩ : AnySignature K) := by
  refine ⟨?_,?_⟩
  · intro zero
    apply hf.1
    have h := congrArg (value mask) zero
    simpa only [value_twice,value_zero] using h
  · rintro ⟨a,b,⟨S⟩⟩
    have S' := split S mask
    rw [value_twice] at S'
    exact hf.2 ⟨_,_,⟨S'⟩⟩

theorem prime_iff (mask : Fin n→Bool) (f : Signature K n) :
    Prime (⟨n,value mask f⟩ : AnySignature K) ↔ Prime (⟨n,f⟩ : AnySignature K) := by
  constructor
  · intro h
    have h' := prime mask (value mask f) h
    rwa [value_twice] at h'
  · exact prime mask f


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBitFlip
end
