import Holant.Proofs.Recognition.RuntimeTensorBasisSemantics
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeTensorBasis
import Holant.Proofs.Recognition.TensorDecisionMatching
import Holant.Proofs.Recognition.RuntimeTensorRowsSoundness

/-! Exact interpretation of the physically emitted matrix pins. The two root
positions are the original allocator's generated I and positive sqrt(2) bindings.
Only identity, the manuscript K, and its prescribed KX orientation occur. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasis
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem compilerData : RationalCompiler.data=RationalCompiler.field.toArithmeticData := rfl

def entryValue {E : Type*} [Field E] (φ : ℚ →+* E) (native opposite : Bool) (_imaginary _sqrt : E)
    (a b : Bool) : E :=
  if native then if opposite then φ (if a=b then 0 else 1) else φ (if a=b then 1 else 0)
  else φ (if a=b then 1 else 0)

theorem typedEntry_eval {E : Type*} [Field E] (φ : ℚ →+* E) {v : ℕ} (z : Fin v → E)
    (native opposite : Bool) (imaginary sqrt : Fin v) (a b : Bool) :
    SparseEvaluation.evaluate RationalCompiler.field φ z (typedEntry native opposite imaginary sqrt a b)=
      entryValue φ native opposite (z imaginary) (z sqrt) a b := by
  cases native <;> cases a <;> cases b <;> cases opposite <;>
    simp [typedEntry,entryValue,compilerData,typedConstant,RationalCompiler.decode_eq]

def basis (native opposite : Bool) : InvertibleKernel :=
  if native then (if opposite then bitFlipBasis else InvertibleKernel.identity) else InvertibleKernel.identity

theorem half_sqrt : ((algebraMap ℚ AlgebraicComplex) (1/2))*sqrtTwo=sqrtTwo⁻¹ := by
  have hs : sqrtTwo*(2 : AlgebraicComplex)⁻¹=sqrtTwo⁻¹ := by
    apply mul_left_cancel₀ sqrtTwo_ne_zero
    calc
      sqrtTwo*(sqrtTwo*(2 : AlgebraicComplex)⁻¹)=1 := by
        rw [←mul_assoc,←pow_two,sqrtTwo_sq]
        norm_num
      _=sqrtTwo*sqrtTwo⁻¹ := (mul_inv_cancel₀ sqrtTwo_ne_zero).symm
  simpa [div_eq_mul_inv,mul_comm] using hs

theorem entryValue_basis (native opposite a b : Bool) :
    entryValue (algebraMap ℚ AlgebraicComplex) native opposite imaginaryUnit sqrtTwo a b=
      (basis native opposite).matrix a b := by
  have hhalf : sqrtTwo*(2 : AlgebraicComplex)⁻¹=sqrtTwo⁻¹ := by
    simpa [div_eq_mul_inv,mul_comm] using half_sqrt
  cases native <;> cases opposite <;> cases a <;> cases b <;>
    simp [entryValue,basis,TensorDecisionMatching.basis,sourceKBasis,KMatrix,
      InvertibleKernel.identity,InvertibleKernel.comp,bitFlipBasis,Kernel.mul_apply,
      Signature.equality,Signature.disequality,hhalf,div_eq_mul_inv,mul_comm]

theorem typedEntry_basis {v : ℕ} (z : Fin v → AlgebraicComplex)
    (native opposite : Bool) (imaginary sqrt : Fin v)
    (hi : z imaginary=imaginaryUnit) (hs : z sqrt=sqrtTwo) (a b : Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ AlgebraicComplex) z
      (typedEntry native opposite imaginary sqrt a b)=(basis native opposite).matrix a b := by
  rw [typedEntry_eval (algebraMap ℚ AlgebraicComplex) z native opposite imaginary sqrt a b]
  exact entryValue_basis native opposite a b

theorem rows_zero_iff {q : ℕ} (z : Fin (5+q) → AlgebraicComplex)
    (native opposite : Bool) (imaginary sqrt : Fin (5+q))
    (hi : z imaginary=imaginaryUnit) (hs : z sqrt=sqrtTwo) :
    (∀p∈typedRows native opposite imaginary sqrt,
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ AlgebraicComplex) z p=0) ↔
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ AlgebraicComplex) z
      (SparseTransform.guard RationalCompiler.data q)=0 ∧
    SymbolicTransform.matrix (SparseTransform.point z)=(basis native opposite).matrix := by
  simp only [typedRows,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true,
    SparseEvaluation.sub_eval,typedEntry_basis z native opposite imaginary sqrt hi hs,sub_eq_zero]
  have hm (a b : Bool) : SparseEvaluation.evaluate RationalCompiler.field
      (algebraMap ℚ AlgebraicComplex) z (SparseTransform.matrix RationalCompiler.data q a b)=
      SymbolicTransform.matrix (SparseTransform.point z) a b := by
    rw [compilerData,SparseEvaluation.matrix_eval]
  simp only [hm]
  constructor
  · rintro ⟨hg,h00,h01,h10,h11⟩
    refine ⟨hg,?_⟩
    funext a b
    cases a <;> cases b <;> assumption
  · rintro ⟨hg,hm⟩
    exact ⟨hg,congrFun (congrFun hm false) false,congrFun (congrFun hm false) true,
      congrFun (congrFun hm true) false,congrFun (congrFun hm true) true⟩

/-- The polynomial inverse used by the runtime table compiler is exactly the
prescribed inverse, including the KX reversal of output bits. -/
theorem inverse_exact {q : ℕ} (z : Fin (5+q) → AlgebraicComplex)
    (native opposite : Bool) (imaginary sqrt : Fin (5+q))
    (hi : z imaginary=imaginaryUnit) (hs : z sqrt=sqrtTwo)
    (hz : ∀p∈typedRows native opposite imaginary sqrt,
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ AlgebraicComplex) z p=0) :
    SymbolicTransform.inverse (SparseTransform.point z)=(basis native opposite).inverse := by
  obtain ⟨hg,hm⟩ := (rows_zero_iff z native opposite imaginary sqrt hi hs).mp hz
  have hguard : MvPolynomial.eval₂ (RingHom.id AlgebraicComplex) (SparseTransform.point z)
      (SymbolicTransform.guard (Fin q))=0 := by
    rw [SymbolicTransform.eval_guard]
    rw [compilerData,SparseEvaluation.guard_eval] at hg
    simpa only [SparseTransform.point,Sum.elim_inl] using hg
  have hh := (SymbolicTransform.inverse_identities (RingHom.id AlgebraicComplex)
    (SparseTransform.point z) hguard).1
  rw [hm] at hh
  calc
    SymbolicTransform.inverse (SparseTransform.point z)=Kernel.mul Signature.equality
      (SymbolicTransform.inverse (SparseTransform.point z)) := (Kernel.equality_mul _).symm
    _=Kernel.mul (Kernel.mul (basis native opposite).inverse (basis native opposite).matrix)
      (SymbolicTransform.inverse (SparseTransform.point z)) := by rw [(basis native opposite).inverse_matrix]
    _=Kernel.mul (basis native opposite).inverse
      (Kernel.mul (basis native opposite).matrix (SymbolicTransform.inverse (SparseTransform.point z))) :=
        Kernel.mul_assoc _ _ _
    _=(basis native opposite).inverse := by rw [hh,Kernel.mul_equality]

section Mapped
variable {E : Type*} [Field E] [Algebra ℚ E] (ψ : AlgebraicComplex →+* E)

theorem rational_compat (r : ℚ) : ψ ((algebraMap ℚ AlgebraicComplex) r)=(algebraMap ℚ E) r :=
  congrArg (fun f : ℚ →+* E => f r) (Subsingleton.elim (ψ.comp (algebraMap ℚ AlgebraicComplex)) (algebraMap ℚ E))

theorem entryValue_map (native opposite a b : Bool) :
    entryValue (algebraMap ℚ E) native opposite (ψ imaginaryUnit) (ψ sqrtTwo) a b=
      ψ (entryValue (algebraMap ℚ AlgebraicComplex) native opposite imaginaryUnit sqrtTwo a b) := by
  cases native <;> cases opposite <;> cases a <;> cases b <;>
    simp [entryValue,map_mul,map_neg,map_ofNat]

theorem typedEntry_basis_map {v : ℕ} (z : Fin v → E)
    (native opposite : Bool) (imaginary sqrt : Fin v)
    (hi : z imaginary=ψ imaginaryUnit) (hs : z sqrt=ψ sqrtTwo) (a b : Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ E) z
      (typedEntry native opposite imaginary sqrt a b)=ψ ((basis native opposite).matrix a b) := by
  rw [typedEntry_eval (algebraMap ℚ E) z native opposite imaginary sqrt a b]
  exact (entryValue_map ψ native opposite a b).trans (congrArg ψ (entryValue_basis native opposite a b))

theorem rows_zero_iff_map {q : ℕ} (z : Fin (5+q) → E)
    (native opposite : Bool) (imaginary sqrt : Fin (5+q))
    (hi : z imaginary=ψ imaginaryUnit) (hs : z sqrt=ψ sqrtTwo) :
    (∀p∈typedRows native opposite imaginary sqrt,
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ E) z p=0) ↔
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ E) z
      (SparseTransform.guard RationalCompiler.data q)=0 ∧
    SymbolicTransform.matrix (SparseTransform.point z)=(fun a b => ψ ((basis native opposite).matrix a b)) := by
  simp only [typedRows,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true,
    SparseEvaluation.sub_eval,typedEntry_basis_map ψ z native opposite imaginary sqrt hi hs,sub_eq_zero]
  have hm (a b : Bool) : SparseEvaluation.evaluate RationalCompiler.field
      (algebraMap ℚ E) z (SparseTransform.matrix RationalCompiler.data q a b)=
      SymbolicTransform.matrix (SparseTransform.point z) a b := by
    rw [compilerData,SparseEvaluation.matrix_eval]
  simp only [hm]
  constructor
  · rintro ⟨hg,h00,h01,h10,h11⟩
    refine ⟨hg,?_⟩
    funext a b
    cases a <;> cases b <;> assumption
  · rintro ⟨hg,hm⟩
    exact ⟨hg,congrFun (congrFun hm false) false,congrFun (congrFun hm false) true,
      congrFun (congrFun hm true) false,congrFun (congrFun hm true) true⟩

omit [Algebra ℚ E] in
theorem kernel_map_mul (U V : Kernel AlgebraicComplex) :
    Kernel.mul (fun a b => ψ (U a b)) (fun a b => ψ (V a b))=
      (fun a b => ψ (Kernel.mul U V a b)) := by
  funext a b
  simp [Kernel.mul_apply]

omit [Algebra ℚ E] in
theorem kernel_map_equality :
    (fun a b => ψ (Signature.equality a b))=(Signature.equality : Kernel E) := by
  funext a b
  cases a <;> cases b <;> simp [Signature.equality]

/-- This version applies directly to complex-valued RootCode search solutions. -/
theorem inverse_exact_map {q : ℕ} (z : Fin (5+q) → E)
    (native opposite : Bool) (imaginary sqrt : Fin (5+q))
    (hi : z imaginary=ψ imaginaryUnit) (hs : z sqrt=ψ sqrtTwo)
    (hz : ∀p∈typedRows native opposite imaginary sqrt,
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ E) z p=0) :
    SymbolicTransform.inverse (SparseTransform.point z)=(fun a b => ψ ((basis native opposite).inverse a b)) := by
  obtain ⟨hg,hm⟩ := (rows_zero_iff_map ψ z native opposite imaginary sqrt hi hs).mp hz
  have hguard : MvPolynomial.eval₂ ψ (SparseTransform.point z)
      (SymbolicTransform.guard (Fin q))=0 := by
    rw [SymbolicTransform.eval_guard]
    rw [compilerData,SparseEvaluation.guard_eval] at hg
    simpa only [SparseTransform.point,Sum.elim_inl] using hg
  have hh := (SymbolicTransform.inverse_identities ψ (SparseTransform.point z) hguard).1
  rw [hm] at hh
  have hinv : Kernel.mul (fun a b => ψ ((basis native opposite).inverse a b))
      (fun a b => ψ ((basis native opposite).matrix a b))=Signature.equality := by
    rw [kernel_map_mul ψ,(basis native opposite).inverse_matrix,kernel_map_equality ψ]
  calc
    SymbolicTransform.inverse (SparseTransform.point z)=Kernel.mul Signature.equality
      (SymbolicTransform.inverse (SparseTransform.point z)) := (Kernel.equality_mul _).symm
    _=Kernel.mul (Kernel.mul (fun a b => ψ ((basis native opposite).inverse a b))
      (fun a b => ψ ((basis native opposite).matrix a b)))
      (SymbolicTransform.inverse (SparseTransform.point z)) := by rw [hinv]
    _=Kernel.mul (fun a b => ψ ((basis native opposite).inverse a b))
      (Kernel.mul (fun a b => ψ ((basis native opposite).matrix a b))
        (SymbolicTransform.inverse (SparseTransform.point z))) := Kernel.mul_assoc _ _ _
    _=(fun a b => ψ ((basis native opposite).inverse a b)) := by rw [hh,Kernel.mul_equality]

/-- The runtime table entries specialize to the intended original source
transform, rather than to an independently supplied transformed table. -/
theorem entries_source {n q : ℕ} (z : Fin (5+(1+q)) → E)
    (native opposite : Bool) (imaginary sqrt : Fin (5+(1+q)))
    (hi : z imaginary=ψ imaginaryUnit) (hs : z sqrt=ψ sqrtTwo)
    (hz : ∀p∈typedRows native opposite imaginary sqrt,
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ E) z p=0)
    (address : (Fin n → Bool) → Fin (5+(1+q))) (f : Signature AlgebraicComplex n)
    (hbind : ∀x,z (address x)=ψ (f x)) (x : Fin n → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ E) z
      (RuntimeTensorRowsSoundness.entries address x)=ψ ((basis native opposite).symm.action f x) := by
  rw [RuntimeTensorRowsSoundness.entries_eval (algebraMap ℚ E) z address (fun y => ψ (f y)) hbind x,
    inverse_exact_map ψ z native opposite imaginary sqrt hi hs hz]
  simp only [InvertibleKernel.action,InvertibleKernel.symm,Signature.coordinateAction,map_sum,map_mul,map_prod]

omit [Algebra ℚ E] in
theorem rawFiniteTest_map_iff {n : ℕ} (oneHot : Bool) (f : Signature AlgebraicComplex n) :
    RuntimeTensorRowsSoundness.RawFiniteTest oneHot (fun x => ψ (f x)) ↔
      RuntimeTensorRowsSoundness.RawFiniteTest oneHot f := by
  simp only [RuntimeTensorRowsSoundness.RawFiniteTest,RuntimeTensorRowsSoundness.RawNonzeroTest,
    RuntimeTensorRowsSoundness.shapeBranchTest,
    UniformTensorDecisionSyntax.branchTest_map_iff ψ ψ.injective,map_eq_zero_iff ψ ψ.injective]

end Mapped

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics
