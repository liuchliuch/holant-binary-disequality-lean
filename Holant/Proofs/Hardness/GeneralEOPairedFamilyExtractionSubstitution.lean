import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionComponentsFull

/-! Composition and binary-face coordinate maps, independent of weighted
interaction sources and extraction programmes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionInteraction
open Holant Holant.Tractable Function
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {m n k : ℕ}

def compose (p : Fin n → Bool ⊕ Fin k) (q : Fin k → Bool ⊕ Fin m) :
    Fin n → Bool ⊕ Fin m := fun i => Sum.elim Sum.inl q (p i)

theorem substitute_compose (p : Fin n → Bool ⊕ Fin k) (q : Fin k → Bool ⊕ Fin m)
    (z : Fin m → Bool) : T.substitute (compose p q) z=T.substitute p (T.substitute q z) := by
  funext i
  cases h : p i <;> simp [compose,T.substitute,h]

def facePorts (i j : Fin n) (x : Fin n → Bool) : Fin n → Bool ⊕ Fin 2 :=
  fun k => if k=j then Sum.inr 1 else if k=i then Sum.inr 0 else Sum.inl (x k)

theorem face_substitute (f : Signature AlgebraicComplex n) (i j : Fin n)
    (x : Fin n → Bool) (z : Fin 2 → Bool) :
    f (T.substitute (facePorts i j x) z)=GeneralEOPairedFamilyExtractionFullSupport.face f i j x z := by
  apply congrArg f
  funext k
  by_cases hj : k=j
  · subst k
    simp [T.substitute,facePorts]
  · by_cases hi : k=i
    · subst k
      simp [T.substitute,facePorts,hj]
    · simp [T.substitute,facePorts,hj,hi]


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionInteraction
end
