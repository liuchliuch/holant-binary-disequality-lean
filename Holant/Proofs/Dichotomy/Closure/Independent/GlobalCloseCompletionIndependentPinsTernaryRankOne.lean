import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsTernarySlices
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsTernaryNormal

/-! Normalize a nonzero singular two-by-two slice by two independently
invertible column completions. Together with the proved singular-pencil
selection this gives the actual GHZ/W decomposition of every prime ternary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernaryRankOne
open Holant Holant.Tractable Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
namespace T
export GlobalCloseCompletionIndependentPinsTernaryAction (action ports prime_action Orbit orbit_of_action ghz w)
end T
namespace S
export GlobalCloseCompletionIndependentPinsTernarySlices (slice pack pack_slices singular_slice)
end S
namespace N
export GlobalCloseCompletionIndependentPinsTernaryNormal (matrix normal classified)
end N
namespace Alg
export Holant.Tractable.SymmetricBinaryPullback (determinant invertibleOfDeterminant)
end Alg
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false

theorem complete_column (u : Bool→AlgebraicComplex) (nonzero : ∃i,u i≠0) :
    ∃A : InvertibleKernel,∀i,A.matrix i false=u i := by
  by_cases h0 : u false=0
  · have h1 : u true≠0 := by
      obtain ⟨i,hi⟩:=nonzero
      cases i
      · exact (hi h0).elim
      · exact hi
    have det : Alg.determinant (N.matrix (u false) 1 (u true) 0)≠0 := by
      simpa [Alg.determinant,N.matrix] using neg_ne_zero.mpr h1
    exact ⟨Alg.invertibleOfDeterminant (N.matrix (u false) 1 (u true) 0) det,fun i=>by cases i <;> rfl⟩
  · have det : Alg.determinant (N.matrix (u false) 0 (u true) 1)≠0 := by
      simpa [Alg.determinant,N.matrix] using h0
    exact ⟨Alg.invertibleOfDeterminant (N.matrix (u false) 0 (u true) 1) det,fun i=>by cases i <;> rfl⟩

theorem rankone_minor (M : Kernel AlgebraicComplex) (singular : Alg.determinant M=0)
    (i j a b : Bool) : M i j*M a b=M i b*M a j := by
  simp only [Alg.determinant] at singular
  cases i <;> cases j <;> cases a <;> cases b
  all_goals first | ring | linear_combination singular | linear_combination -singular

theorem rankone_columns (M : Kernel AlgebraicComplex) (nonzero : M≠0) (singular : Alg.determinant M=0) :
    ∃A B : InvertibleKernel,∀i j,M i j=A.matrix i false*B.matrix j false := by
  classical
  have exists_live : ∃i j,M i j≠0 := by
    by_contra bad
    push_neg at bad
    exact nonzero (funext fun i=>funext fun j=>bad i j)
  obtain ⟨a,b,live⟩:=exists_live
  obtain ⟨A,hA⟩:=complete_column (fun i=>M i b) ⟨a,live⟩
  obtain ⟨B,hB⟩:=complete_column (fun j=>M a j/M a b) ⟨b,by rw [div_self live];exact one_ne_zero⟩
  refine ⟨A,B,?_⟩
  intro i j
  rw [hA,hB]
  field_simp [live]
  exact rankone_minor M singular i j a b

theorem last_action (B C : InvertibleKernel) (f : Signature AlgebraicComplex 3) (v : Bool) :
    S.slice (T.action InvertibleKernel.identity B C f) v=
      Kernel.mul (Kernel.mul B.matrix (S.slice f v)) (Kernel.transpose C.matrix) := by
  funext i j
  simp only [S.slice,T.action,Signature.coordinateAction,GlobalCloseCompletionTernaryGHZAction.sum_words]
  cases v <;> simp [T.ports,InvertibleKernel.identity,Fin.prod_univ_three,Signature.equality,
    Kernel.mul_apply,Kernel.transpose,S.slice]
  all_goals ring

def e00 : Kernel AlgebraicComplex:=fun i j=>if i then 0 else if j then 0 else 1

theorem normalize_columns (A B : InvertibleKernel) (M : Kernel AlgebraicComplex)
    (form : ∀i j,M i j=A.matrix i false*B.matrix j false) :
    Kernel.mul (Kernel.mul A.inverse M) (Kernel.transpose B.inverse)=e00 := by
  funext i j
  have ha:=congrFun₂ A.inverse_matrix i false
  have hb:=congrFun₂ B.inverse_matrix j false
  simp only [Kernel.mul_apply] at ha hb
  calc
    _=(A.inverse i false*A.matrix false false+A.inverse i true*A.matrix true false)*
      (B.inverse j false*B.matrix false false+B.inverse j true*B.matrix true false) := by
      simp only [Kernel.mul_apply,Kernel.transpose,form]
      ring
    _=Signature.equality i false*Signature.equality j false := by rw [ha,hb]
    _=e00 i j := by cases i <;> cases j <;> simp [e00,Signature.equality]

theorem normal_form (f : Signature AlgebraicComplex 3) (form : S.slice f true=e00) :
    f=N.normal (S.slice f false false false) (S.slice f false false true)
      (S.slice f false true false) (S.slice f false true true) := by
  funext x
  have word : ![x 0,x 1,x 2]=x := by funext i;fin_cases i <;> rfl
  have hf:=congrFun₂ form (x 1) (x 2)
  change f ![true,x 1,x 2]=e00 (x 1) (x 2) at hf
  have hx:=congrArg f word
  cases e0 : x 0 <;> cases e1 : x 1 <;> cases e2 : x 2 <;>
    simp [N.normal,N.matrix,S.slice,e00,e0,e1,e2] at hf hx ⊢
  all_goals first | exact hx.symm | exact hx.symm.trans hf

theorem classified (f : Signature AlgebraicComplex 3)
    (prime : Prime (⟨3,f⟩ : AnySignature AlgebraicComplex)) : T.Orbit f := by
  obtain ⟨A,live,singular⟩:=S.singular_slice f prime
  let g:=T.action A InvertibleKernel.identity InvertibleKernel.identity f
  have pg : Prime (⟨3,g⟩ : AnySignature AlgebraicComplex):=T.prime_action f prime (T.ports A InvertibleKernel.identity InvertibleKernel.identity)
  obtain ⟨B,C,form⟩:=rankone_columns (S.slice g true) live singular
  let h:=T.action InvertibleKernel.identity B.symm C.symm g
  have ph : Prime (⟨3,h⟩ : AnySignature AlgebraicComplex):=T.prime_action g pg (T.ports InvertibleKernel.identity B.symm C.symm)
  have normalized : S.slice h true=e00 := by
    rw [last_action]
    exact normalize_columns B C (S.slice g true) form
  have hform:=normal_form h normalized
  have ho : T.Orbit h := by
    rw [hform] at ph ⊢
    exact N.classified _ _ _ _ ph
  exact T.orbit_of_action A InvertibleKernel.identity InvertibleKernel.identity f
    (T.orbit_of_action InvertibleKernel.identity B.symm C.symm g ho)

theorem decomposition (f : Signature AlgebraicComplex 3)
    (prime : Prime (⟨3,f⟩ : AnySignature AlgebraicComplex)) :
    (∃A B C : InvertibleKernel,f=GlobalCloseCompletionTernaryGHZCore.ghz A.matrix B.matrix C.matrix) ∨
    (∃A B C : InvertibleKernel,f=GlobalCloseCompletionIndependentPinsWGeneralCore.image A.matrix B.matrix C.matrix) := by
  rcases classified f prime with ⟨A,B,C,form⟩|⟨A,B,C,form⟩
  · exact Or.inl ⟨A,B,C,form.trans (T.ghz A B C)⟩
  · exact Or.inr ⟨A,B,C,form.trans (T.w A B C)⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsTernaryRankOne
end
