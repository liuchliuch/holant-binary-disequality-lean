import Holant.Certificates.EqualityQuaternary.PhysicalFlip
import Holant.Tensor

/-! Genuine factorization across arbitrary nonempty original-port cuts.
The nonmatching conclusion follows from primality, not from an assumed rank
or matching-classification certificate. -/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas

def ProperFactor (q : Signature Scalar 4) : Prop :=
  ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ ∃ ports : (Fin m ⊕ Fin n) ≃ Fin 4,
    ∃ f : Signature Scalar m, ∃ g : Signature Scalar n,
      q = Tensor.reindex ports (Tensor.tensor f g)

def TensorPrime (q : Signature Scalar 4) : Prop := q ≠ 0 ∧ ¬ProperFactor q

/-- Actual binary factors on an arbitrary perfect matching, with its scalar. -/
def GroupMatching (G : Set Mat) (q : Signature Scalar 4) : Prop :=
  ∃ ports : (Fin 2 ⊕ Fin 2) ≃ Fin 4, ∃ A ∈ G, ∃ B ∈ G, ∃ c : Scalar,
    c ≠ 0 ∧ q = Tensor.reindex ports
      (Tensor.tensor (fun x => c * kernelSignature A x) (kernelSignature B))

theorem matching_proper {G : Set Mat} {q : Signature Scalar 4} (h : GroupMatching G q) :
    ProperFactor q := by
  obtain ⟨p,A,_,B,_,c,_,h⟩ := h
  exact ⟨2,2,by decide,by decide,p,_,_,h⟩

theorem prime_not_matching {G : Set Mat} {q : Signature Scalar 4} (h : TensorPrime q) :
    ¬GroupMatching G q := fun hm => h.2 (matching_proper hm)

theorem flip_twice (q : Signature Scalar 4) (mask : Word) :
    Flip.value (Flip.value q mask) mask = q := by
  funext x
  apply congrArg q
  funext i
  simp [Flip.value,xorWord]

theorem flip_proper {q : Signature Scalar 4} (h : ProperFactor q) (mask : Word) :
    ProperFactor (Flip.value q mask) := by
  obtain ⟨m,n,hm,hn,p,f,g,hq⟩ := h
  refine ⟨m,n,hm,hn,p,
    (fun x => f (fun i => x i ^^ mask (p (.inl i)))),
    (fun x => g (fun i => x i ^^ mask (p (.inr i)))),?_⟩
  funext x
  rw [Flip.value,hq]
  rfl

theorem flip_prime {q : Signature Scalar 4} (h : TensorPrime q) (mask : Word) :
    TensorPrime (Flip.value q mask) := by
  constructor
  · intro hz
    have hh := flip_twice q mask
    rw [hz] at hh
    exact h.1 hh.symm
  · intro hp
    have hh := flip_proper hp mask
    rw [flip_twice] at hh
    exact h.2 hh

end Holant.Certificates.EqualityQuaternary
