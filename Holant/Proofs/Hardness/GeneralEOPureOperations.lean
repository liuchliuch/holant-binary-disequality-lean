import Holant.Proofs.Hardness.GeneralEOPureAffineSpan
import Holant.Proofs.Hardness.GeneralEOCentralHoleCoordinates
import Mathlib.Data.List.Induction

/-! Pure and common-sign support are inherited by complementary slices and
boundary permutations. These are semantic identities used by native loops. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureOperations
open Holant Holant.Tractable GeneralEODEQProducerSupportBasic
namespace O
export GeneralEOPinnedDescentOperations (word word_weight)
end O
namespace S
export GeneralEOCentralHoleStep (word_xor complementary_charge)
end S
namespace N
export GeneralEOPinnedDescentNetwork (reboundary reboundary_denote)
end N
namespace C
export GeneralEOCentralHoleCoordinates (charge_comp xor_comp)
end C
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

/-- Odd affine combinations preserve a common pair of pinned coordinates. -/
theorem xorList_word (u v : Bool) (xs : List (Fin n → Bool)) (ho : Odd xs.length) :
    xorList (xs.map (O.word u v))=O.word u v (xorList xs) := by
  induction xs using List.twoStepInduction with
  | nil => simp at ho
  | singleton x =>
    have h : xorList [x]=x := by funext i; simp [xorList]
    rw [h]
    funext i
    simp [xorList]
  | cons_cons x y xs ih _ =>
    have hodd : Odd xs.length := by
      rw [Nat.odd_iff] at ho ⊢
      simp only [List.length_cons] at ho
      omega
    funext i
    simp only [List.map_cons,xorList_cons,ih hodd]
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · change Bool.xor u (Bool.xor u u)=u
      cases u <;> rfl
    · change Bool.xor v (Bool.xor v v)=v
      cases v <;> rfl
    · rfl

def slice (f : Signature AlgebraicComplex (n+2)) (b : Bool) : Signature AlgebraicComplex n :=
  fun x => f (O.word b (!b) x)

theorem slice_pure (f : Signature AlgebraicComplex (n+2)) (sign : EOSign)
    (hp : Pure sign f) (b : Bool) : Pure sign (slice f b) := by
  intro xs ho hs
  have h := hp (xs.map (O.word b (!b))) (by simpa using ho) (by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact hs y hy)
  rw [xorList_word b (!b) xs ho,S.complementary_charge] at h
  exact h

theorem slice_supports (f : Signature AlgebraicComplex (n+2)) (sign : EOSign)
    (hs : EONegativeWitness.Supports sign ⟨n+2,f⟩) (b : Bool) :
    EONegativeWitness.Supports sign ⟨n,slice f b⟩ := by
  intro x y z hx hy hz
  have h := hs (O.word b (!b) x) (O.word b (!b) y) (O.word b (!b) z) hx hy hz
  rw [S.word_xor] at h
  simp only [Bool.xor_self,Bool.false_xor] at h
  rw [S.complementary_charge] at h
  exact h

theorem slice_central (f : Signature AlgebraicComplex (n+2))
    (he : Signature.CentralSupport f) (b : Bool) : Signature.CentralSupport (slice f b) := by
  intro x hx
  apply he
  rw [O.word_weight]
  cases b <;> simp only [Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false] <;> omega

theorem xorList_comp (xs : List (Fin n → Bool)) (e : Fin m ≃ Fin n) :
    xorList (xs.map (fun x => x ∘ e))=xorList xs ∘ e := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    funext i
    simp only [List.map_cons,xorList_cons,ih,Function.comp_apply]

theorem reindex_pure (f : Signature AlgebraicComplex n) (sign : EOSign)
    (hp : Pure sign f) (e : Fin n ≃ Fin m) : Pure sign (Tensor.reindex e f) := by
  intro xs ho hs
  have h := hp (xs.map (fun x => x ∘ e)) (by simpa using ho) (by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact hs y hy)
  rw [xorList_comp,C.charge_comp] at h
  exact h

theorem reindex_supports (f : Signature AlgebraicComplex n) (sign : EOSign)
    (hs : EONegativeWitness.Supports sign ⟨n,f⟩) (e : Fin n ≃ Fin m) :
    EONegativeWitness.Supports sign ⟨m,Tensor.reindex e f⟩ := by
  intro x y z hx hy hz
  have h := hs (x ∘ e) (y ∘ e) (z ∘ e) hx hy hz
  rw [C.xor_comp,C.charge_comp] at h
  exact h

theorem reboundary_pure (T : Network AlgebraicComplex n) (sign : EOSign)
    (hp : Pure sign T.denote) (e : Fin n ≃ Fin m) : Pure sign (N.reboundary T e).denote := by
  rw [N.reboundary_denote]
  exact reindex_pure T.denote sign hp e

theorem reboundary_supports (T : Network AlgebraicComplex n) (sign : EOSign)
    (hs : EONegativeWitness.Supports sign ⟨n,T.denote⟩) (e : Fin n ≃ Fin m) :
    EONegativeWitness.Supports sign ⟨m,(N.reboundary T e).denote⟩ := by
  rw [N.reboundary_denote]
  exact reindex_supports T.denote sign hs e

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureOperations
