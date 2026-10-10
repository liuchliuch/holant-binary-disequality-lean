import Holant.OpenNetworkComposition.Finite

/-! Explicit original-port injections for two disjoint open gadgets. -/
namespace Holant.OpenNetworkComposition
variable {VL VR FL FR : Type*} (aL : VL → ℕ) (aR : VR → ℕ)

abbrev SumArity := Sum.elim aL aR

def leftPort : Ports VL FL aL ↪ Ports (VL ⊕ VR) (FL ⊕ FR) (SumArity aL aR) where
  toFun
    | .inl ⟨v,i⟩ => .inl ⟨.inl v,i⟩
    | .inr f => .inr (.inl f)
  inj' := by
    rintro (⟨v,i⟩ | f) (⟨w,j⟩ | g) h
    · cases h; rfl
    · cases h
    · cases h
    · cases h; rfl

def rightPort : Ports VR FR aR ↪ Ports (VL ⊕ VR) (FL ⊕ FR) (SumArity aL aR) where
  toFun
    | .inl ⟨v,i⟩ => .inl ⟨.inr v,i⟩
    | .inr f => .inr (.inr f)
  inj' := by
    rintro (⟨v,i⟩ | f) (⟨w,j⟩ | g) h
    · cases h; rfl
    · cases h
    · cases h
    · cases h; rfl

@[simp] theorem left_right_ne (p : Ports VL FL aL) (q : Ports VR FR aR) :
    leftPort aL aR p≠rightPort aL aR q := by
  rintro h
  cases p with
  | inl p => cases q with
    | inl q =>
      have hf := congrArg Sigma.fst (Sum.inl.inj h)
      cases hf
    | inr q => cases h
  | inr p => cases q with
    | inl q => cases h
    | inr q => cases h

@[simp] theorem right_left_ne (p : Ports VR FR aR) (q : Ports VL FL aL) :
    rightPort aL aR p≠leftPort aL aR q := (left_right_ne aL aR q p).symm

def portSum : Ports (VL ⊕ VR) (FL ⊕ FR) (SumArity aL aR) ≃ (Ports VL FL aL ⊕ Ports VR FR aR) where
  toFun
    | .inl ⟨.inl v,i⟩ => .inl (.inl ⟨v,i⟩)
    | .inl ⟨.inr v,i⟩ => .inr (.inl ⟨v,i⟩)
    | .inr (.inl f) => .inl (.inr f)
    | .inr (.inr f) => .inr (.inr f)
  invFun := Sum.elim (leftPort aL aR) (rightPort aL aR)
  left_inv := by
    rintro (⟨v,i⟩ | f)
    · cases v <;> rfl
    · cases f <;> rfl
  right_inv := by rintro ((⟨v,i⟩ | f) | (⟨v,i⟩ | f)) <;> rfl

@[simp] theorem portSum_left (p : Ports VL FL aL) : portSum (FR := FR) aL aR (leftPort aL aR p)=Sum.inl p := by
  cases p <;> rfl
@[simp] theorem portSum_right (p : Ports VR FR aR) : portSum (FL := FL) aL aR (rightPort aL aR p)=Sum.inr p := by
  cases p <;> rfl

end Holant.OpenNetworkComposition
