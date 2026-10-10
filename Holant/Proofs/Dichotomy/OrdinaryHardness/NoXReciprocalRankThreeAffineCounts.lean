import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeAffineCertificate

/-! The affine repair certificate is lifted to all original natural counts. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeAffineCounts
open scoped BigOperators
namespace A
export NoXReciprocalRankThreeAffinePorts (Transform offset)
end A
namespace P
export OrdinaryNegativeSparseRankThreeParity (image)
end P
namespace D
export NoXReciprocalRankThreeAffineData (inputBit contribution schedule)
end D
namespace C
export NoXReciprocalRankThreeAffineCertificates (certificate)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable (v : Fin 7→Bool→ℕ) (side : Bool) (q : Fin 126)
variable (countsMatch : ∀i b,v i b%2=if D.inputBit side q i b then 1 else 0)
def contribution (t : A.Transform) (j : Fin 7) (b : Bool) : ℕ :=
  ∑i : Fin 7,if P.image t.base i=j.succ then v i (b ^^ A.offset t i) else 0

include countsMatch in
theorem contribution_mod (t : A.Transform) (j : Fin 7) (b : Bool) :
    contribution v t j b%2=D.contribution side q t j b%2 := by
  unfold contribution D.contribution
  rw [Finset.sum_nat_mod,Finset.sum_nat_mod]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h:P.image t.base i=j.succ
  · simp only [h,ite_true,true_and,countsMatch]
    cases hb:D.inputBit side q i (b ^^ A.offset t i) <;> simp [hb]
  · simp [h]

def total (j : Fin 7) (b : Bool) : ℕ :=
  v j b+∑k : Fin 13,contribution v (D.schedule side q k) j b

include countsMatch in
theorem total_even (j : Fin 7) (b : Bool) : Even (total v side q j b) := by
  have h:=C.certificate q side j b
  rw [Nat.even_iff,total,Nat.add_mod,Finset.sum_nat_mod]
  simp_rw [countsMatch,contribution_mod v side q countsMatch]
  rw [Nat.add_mod,Finset.sum_nat_mod] at h
  have small : (if D.inputBit side q j b then 1 else 0)%2=(if D.inputBit side q j b then 1 else 0) := by
    cases D.inputBit side q j b <;> rfl
  rw [small] at h
  exact h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeAffineCounts
