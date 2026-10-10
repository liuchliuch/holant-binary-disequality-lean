import Holant.Dihedral.CompatibleCoefficientLine.PortAlignment
import Holant.Dihedral.CompatibleClosure.GroupFusion

/-! Equal actual matching involutions determine a literal edge permutation
and the necessary individual endpoint reversals.  The whole coefficient
product is preserved, including its original global scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.EndpointParallelogram

variable {n r : ℕ}

def edgeIndex (p₀ p₁ : (Fin r × Bool) ≃ Fin n) (e : Fin r) : Fin r :=
  (p₁.symm (p₀ (e,false))).1

def edgeReversed (p₀ p₁ : (Fin r × Bool) ≃ Fin n) (e : Fin r) : Bool :=
  (p₁.symm (p₀ (e,false))).2

theorem aligned_endpoint (p₀ p₁ : (Fin r × Bool) ≃ Fin n)
    (same : (Pairing.ofPorts p₀).mate = (Pairing.ofPorts p₁).mate)
    (e : Fin r) (b : Bool) :
    p₁ (edgeIndex p₀ p₁ e,b ^^ edgeReversed p₀ p₁ e) = p₀ (e,b) := by
  cases b
  · simpa only [edgeIndex,edgeReversed,Bool.false_xor,Prod.mk.eta]
      using p₁.apply_symm_apply (p₀ (e,false))
  · have h := congrFun same (p₀ (e,false))
    simp only [Pairing.ofPorts,Equiv.symm_apply_apply,Bool.not_false] at h
    simpa only [edgeIndex,edgeReversed,Bool.true_xor] using h.symm

theorem edgeIndex_injective (p₀ p₁ : (Fin r × Bool) ≃ Fin n)
    (same : (Pairing.ofPorts p₀).mate = (Pairing.ofPorts p₁).mate) :
    Function.Injective (edgeIndex p₀ p₁) := by
  intro e f equal
  have xorIdentity (a b : Bool) : ((a ^^ b) ^^ b) = a := by
    cases a <;> cases b <;> decide
  have h : p₀ (e,false) = p₀ (f,edgeReversed p₀ p₁ e ^^ edgeReversed p₀ p₁ f) := by
    rw [← aligned_endpoint p₀ p₁ same e false,
      ← aligned_endpoint p₀ p₁ same f (edgeReversed p₀ p₁ e ^^ edgeReversed p₀ p₁ f)]
    simp only [Bool.false_xor,xorIdentity,equal]
  exact congrArg Prod.fst (p₀.injective h)

def edgePermutation (p₀ p₁ : (Fin r × Bool) ≃ Fin n)
    (same : (Pairing.ofPorts p₀).mate = (Pairing.ofPorts p₁).mate) : Equiv.Perm (Fin r) :=
  Equiv.ofBijective (edgeIndex p₀ p₁)
    ⟨edgeIndex_injective p₀ p₁ same,Finite.surjective_of_injective (edgeIndex_injective p₀ p₁ same)⟩

def alignedFactor (p₀ p₁ : (Fin r × Bool) ≃ Fin n) (A : Fin r → Mat) (e : Fin r) : Mat :=
  if edgeReversed p₀ p₁ e then Kernel.transpose (A (edgeIndex p₀ p₁ e))
  else A (edgeIndex p₀ p₁ e)

/-- No equality of arbitrary ordered edge lists is assumed.  The factors are
reindexed and transposed from their actual source presentation, and the exact
original coefficient tensor and scalar are retained. -/
theorem aligned_product (p₀ p₁ : (Fin r × Bool) ≃ Fin n)
    (same : (Pairing.ofPorts p₀).mate = (Pairing.ofPorts p₁).mate)
    (A : Fin r → Mat) (κ : Scalar) :
    productValue p₀ (alignedFactor p₀ p₁ A) κ = productValue p₁ A κ := by
  funext x
  change κ * (∏ e,alignedFactor p₀ p₁ A e (x (p₀ (e,false))) (x (p₀ (e,true)))) = _
  apply congrArg (κ * ·)
  rw [← Equiv.prod_comp (edgePermutation p₀ p₁ same)
    (fun e => A e (x (p₁ (e,false))) (x (p₁ (e,true))))]
  apply Finset.prod_congr rfl
  intro e _
  change alignedFactor p₀ p₁ A e (x (p₀ (e,false))) (x (p₀ (e,true))) =
    A (edgeIndex p₀ p₁ e) (x (p₁ (edgeIndex p₀ p₁ e,false)))
      (x (p₁ (edgeIndex p₀ p₁ e,true)))
  rw [← aligned_endpoint p₀ p₁ same e false,← aligned_endpoint p₀ p₁ same e true]
  cases h : edgeReversed p₀ p₁ e <;> simp [alignedFactor,h,Kernel.transpose]

theorem alignedFactor_group {m : ℕ} (hm : 0 < m)
    (p₀ p₁ : (Fin r × Bool) ≃ Fin n) (A : Fin r → Mat)
    (valid : ∀ e,A e ∈ groupM m) (e : Fin r) :
    alignedFactor p₀ p₁ A e ∈ groupM m := by
  unfold alignedFactor
  split
  · exact transpose_group_mem hm (valid _)
  · exact valid _

/-- Endpoint reversal changes the ordered coefficients but preserves their
support parity.  This is needed when comparing real per-edge parity tags. -/
theorem hasParity_transpose {α : Bool} {A : Mat} (h : HasParity α A) :
    HasParity α (Kernel.transpose A) := by
  obtain ⟨w,nonzero,rfl⟩ := h
  exact ⟨fun a => w (a ^^ α),fun a => nonzero _,monomial_transpose α w⟩

theorem alignedFactor_parity (p₀ p₁ : (Fin r × Bool) ≃ Fin n)
    (A : Fin r → Mat) (α : Fin r → Bool)
    (valid : ∀ e,HasParity (α e) (A e)) (e : Fin r) :
    HasParity (α (edgeIndex p₀ p₁ e)) (alignedFactor p₀ p₁ A e) := by
  unfold alignedFactor
  split
  · exact hasParity_transpose (valid _)
  · exact valid _

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
