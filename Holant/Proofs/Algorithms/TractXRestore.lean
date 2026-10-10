import Holant.Tractable.Criteria
import Holant.Tractable.Downward


namespace Holant.LocalDrafts.MainChain.TractXRestore
open Holant.Tractable
noncomputable section

 theorem nullary_eq_scalar (f : Signature AlgebraicComplex 0) :
    f = Signature.scalar (f Fin.elim0) := by
  funext x
  exact congrArg f (Subsingleton.elim x Fin.elim0)

/-- The empty tensor decomposition retains the actual nonzero nullary scalar. -/
theorem nullary_tensorClosure (C : (n : ℕ) → Signature AlgebraicComplex n → Prop)
    (f : Signature AlgebraicComplex 0) : SourceTensorClosure C f := by
  by_cases hz : f = 0
  · exact Or.inl hz
  · right
    have hn : f Fin.elim0 ≠ 0 := by
      intro h
      apply hz
      rw [nullary_eq_scalar f, h]
      rfl
    let D : TensorDecomposition AlgebraicComplex 0 := {
      count := 0
      arity := fun i => Fin.elim0 i
      factor := fun i => Fin.elim0 i
      ports := {
        toFun := fun p => Fin.elim0 p.1
        invFun := fun i => Fin.elim0 i
        left_inv := fun p => Fin.elim0 p.1
        right_inv := fun i => Fin.elim0 i }
      scale := Units.mk0 (f Fin.elim0) hn }
    refine ⟨D, (fun i => Fin.elim0 i), ?_⟩
    funext x
    have hx : x = Fin.elim0 := Subsingleton.elim _ _
    simp [TensorDecomposition.value, D, hx]

 theorem arityTwo_restore {F : SignatureFamily AlgebraicComplex}
    (h : ArityTwoAlternative (preprocess F)) : ArityTwoAlternative F := by
  rintro ⟨n,f⟩ hf
  by_cases hz : f = 0
  · exact Or.inl hz
  · cases n with
    | zero => exact nullary_tensorClosure _ f
    | succ n => exact h ⟨n+1,f⟩ ⟨hf, Nat.succ_pos n, hz⟩

/-- A tensor class also admits every nullary scalar via the empty tensor
product, so either fixed matching orientation survives source preprocessing. -/
theorem matching_restore {F : SignatureFamily AlgebraicComplex}
    (h : MatchingAlternative (preprocess F)) : MatchingAlternative F := by
  have lift (opposite : Bool)
      (hC : ∀ f ∈ preprocess F, SourceTensorClosure (matchingImage opposite) f.2) :
      ∀ f ∈ F, SourceTensorClosure (matchingImage opposite) f.2 := by
    rintro ⟨n,f⟩ hf
    by_cases hz : f = 0
    · exact Or.inl hz
    · cases n with
      | zero => exact nullary_tensorClosure _ f
      | succ n => exact hC ⟨n+1,f⟩ ⟨hf,Nat.succ_pos n,hz⟩
  rcases h with h | h
  · exact Or.inl (lift false h)
  · exact Or.inr (lift true h)

/-- Pure structural closure, instantiated below only with the actual A/P/L
classes and their proved zero/nullary membership. -/
theorem common_restore (C : SignatureFamily AlgebraicComplex)
    (hzero : ∀ n, (⟨n,0⟩ : AnySignature AlgebraicComplex) ∈ C)
    (hscalar : ∀ c, (⟨0,Signature.scalar c⟩ : AnySignature AlgebraicComplex) ∈ C)
    {F : SignatureFamily AlgebraicComplex} (hfin : F.Finite)
    (h : CommonTransformable C (preprocess F)) : CommonTransformable C F := by
  obtain ⟨_,B,hE,hG⟩ := h
  refine ⟨hfin,B,hE,?_⟩
  rintro ⟨n,f⟩ hf
  by_cases hz : f = 0
  · subst f
    simpa only [InvertibleKernel.action,Signature.coordinateAction_zero] using hzero n
  · cases n with
    | zero =>
      change (⟨0,B.symm.action f⟩ : AnySignature AlgebraicComplex) ∈ C
      rw [nullary_eq_scalar (B.symm.action f)]
      exact hscalar _
    | succ n => exact hG ⟨n+1,f⟩ ⟨hf,Nat.succ_pos n,hz⟩

 theorem affine_restore {F : SignatureFamily AlgebraicComplex} (hfin : F.Finite)
    (h : CommonTransformable affineClass (preprocess F)) : CommonTransformable affineClass F :=
  common_restore affineClass (fun n => affine_zero n)
    (fun c => affine_constant 0 c) hfin h

 theorem product_restore {F : SignatureFamily AlgebraicComplex} (hfin : F.Finite)
    (h : CommonTransformable productClass (preprocess F)) : CommonTransformable productClass F :=
  common_restore productClass (fun n => product_zero n)
    (fun c => product_constant 0 c) hfin h

 theorem localAffine_restore {F : SignatureFamily AlgebraicComplex} (hfin : F.Finite)
    (h : CommonTransformable localAffineClass (preprocess F)) : CommonTransformable localAffineClass F :=
  common_restore localAffineClass (fun n => localAffine_zero n)
    localAffine_scalar hfin h

/-- No source family member is deleted at runtime on the tractable branch.
The zero/nullary cases are covered by the original evaluator's real input type. -/
theorem core_restore {F : SignatureFamily AlgebraicComplex} (hfin : F.Finite)
    (h : TractXCore (preprocess F)) : TractXCore F := by
  rcases h with h | h | h | h
  · exact Or.inl (arityTwo_restore h)
  · exact Or.inr (Or.inl (affine_restore hfin h))
  · exact Or.inr (Or.inr (Or.inl (product_restore hfin h)))
  · exact Or.inr (Or.inr (Or.inr (localAffine_restore hfin h)))

 theorem source_criterion_core {F : SignatureFamily AlgebraicComplex} (hfin : F.Finite)
    (h : TractX F) : TractXCore F := core_restore hfin h.2

end
end Holant.LocalDrafts.MainChain.TractXRestore
