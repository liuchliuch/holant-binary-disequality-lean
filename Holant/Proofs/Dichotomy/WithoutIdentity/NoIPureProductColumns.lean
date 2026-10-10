import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureUniformFour
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleSupport

/-! Exact signed incidence for a full logical face. Staying in one Hamming
weight class modulo four forces each free component's positive-minus-negative
original-port multiplicity to be divisible by four. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductColumns
open Holant Holant.Tractable
open scoped BigOperators
namespace S
export OrdinaryNegativeNonproductBundleSupport (signedWord flip Face)
end S
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {n m : ℕ}

def column (base : Fin n→Bool) (ports : Fin n→Bool ⊕ Fin m) (j : Fin m) : ℤ:=
  ∑i : Fin n,if ports i=Sum.inr j then (if base i then -1 else 1) else 0

theorem weight_difference (base : Fin n→Bool) (ports : Fin n→Bool ⊕ Fin m) (j : Fin m) :
    (weight (S.signedWord base ports (fun k=>decide (k=j))) : ℤ)-
      weight (S.signedWord base ports (fun _=>false))=column base ports j := by
  classical
  unfold weight column
  simp only [Nat.cast_sum]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : ports i with
  | inl bit=>simp [S.signedWord,S.flip,T.substitute,hp]
  | inr k=>
    by_cases hk : k=j
    · subst k
      cases hb : base i <;> simp [S.signedWord,S.flip,T.substitute,hp,hb]
    · simp [S.signedWord,S.flip,T.substitute,hp,hk]

theorem divisible {K : Type*} [Zero K] (f : Signature K n) (base : Fin n→Bool)
    (ports : Fin n→Bool ⊕ Fin m) (uniform : NoIPureChargeTwoFamily.UniformFour f)
    (full : ∀z,f (S.signedWord base ports z)≠0) (j : Fin m) : column base ports j%4=0 := by
  have same:=uniform (S.signedWord base ports (fun k=>decide (k=j)))
    (S.signedWord base ports (fun _=>false)) (full _) (full _)
  have difference:=weight_difference base ports j
  omega

theorem face {f : Signature AlgebraicComplex n} (D : S.Face f)
    (uniform : NoIPureChargeTwoFamily.UniformFour f) (j : Fin 2) : column D.base D.ports j%4=0 :=
  divisible f D.base D.ports uniform D.full j


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductColumns
end
