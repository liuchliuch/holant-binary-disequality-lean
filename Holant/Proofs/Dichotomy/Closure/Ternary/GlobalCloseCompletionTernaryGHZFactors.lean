import Holant.Tractable.CommonTransform
import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist

/-! Generic common-basis action preserves every exact tensor split and prime.
This focused proof avoids unrelated historical execution dependencies. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZFactors
open Holant Holant.Tractable Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
def actAny (U : InvertibleKernel) (f : AnySignature AlgebraicComplex) :
    AnySignature AlgebraicComplex := ⟨f.1,U.action f.2⟩

@[simp] theorem actAny_inverse (U : InvertibleKernel) (f : AnySignature AlgebraicComplex) :
    actAny U.symm (actAny U f) = f := by
  cases f
  simp [actAny]

theorem action_scale (U : InvertibleKernel) {n : ℕ} (c : AlgebraicComplex)
    (f : Signature AlgebraicComplex n) : U.action (c • f) = c • U.action f := by
  funext x
  simp only [InvertibleKernel.action,Signature.coordinateAction,Pi.smul_apply,smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem action_zero_iff (U : InvertibleKernel) {n : ℕ} (f : Signature AlgebraicComplex n) :
    U.action f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have he := congrArg U.symm.action h
    rw [InvertibleKernel.symm_action_action] at he
    simpa only [InvertibleKernel.action,Signature.coordinateAction_zero] using he
  · rintro rfl
    exact Signature.coordinateAction_zero _

theorem action_product (U : InvertibleKernel) {r m n : ℕ}
    (p : (Fin m ⊕ Fin n) ≃ Fin r) (f : Signature AlgebraicComplex m)
    (g : Signature AlgebraicComplex n) (c : AlgebraicComplex) :
    U.action (fun x => c * (f (fun i => x (p (.inl i))) * g (fun j => x (p (.inr j))))) =
      fun x => c * (U.action f (fun i => x (p (.inl i))) *
        U.action g (fun j => x (p (.inr j)))) := by
  classical
  let e : (Fin r → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
    (Equiv.arrowCongr p.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) Bool)
  funext x
  simp only [InvertibleKernel.action,Signature.coordinateAction]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [←Fintype.sum_prod_type (fun q : (Fin m → Bool) × (Fin n → Bool) =>
    c * (((∏ i, U.matrix (x (p (.inl i))) (q.1 i)) * f q.1) *
      ((∏ j, U.matrix (x (p (.inr j))) (q.2 j)) * g q.2)))]
  apply Fintype.sum_equiv e
  intro y
  have hp := p.prod_comp (fun i => U.matrix (x i) (y i))
  rw [Fintype.prod_sum_type] at hp
  change (∏ i,U.matrix (x i) (y i)) *
    (c * (f (fun i => y (p (.inl i))) * g (fun j => y (p (.inr j))))) = _
  rw [←hp]
  change _ = c * (((∏ i,U.matrix (x (p (.inl i))) (y (p (.inl i)))) *
    f (fun i => y (p (.inl i)))) *
    ((∏ j,U.matrix (x (p (.inr j))) (y (p (.inr j)))) * g (fun j => y (p (.inr j)))))
  ring

def splitAction (U : InvertibleKernel) {f a b : AnySignature AlgebraicComplex}
    (s : ProperSplit f a b) : ProperSplit (actAny U f) (actAny U a) (actAny U b) where
  left_pos := s.left_pos
  right_pos := s.right_pos
  ports := s.ports
  scale := s.scale
  equation := by
    change U.action f.2 = _
    rw [s.equation,action_product]
    rfl

theorem prime_action_iff (U : InvertibleKernel) (f : AnySignature AlgebraicComplex) :
    Prime (actAny U f) ↔ Prime f := by
  constructor
  · rintro ⟨hn,hp⟩
    refine ⟨fun hz => hn ((action_zero_iff U f.2).mpr hz),?_⟩
    rintro ⟨a,b,⟨s⟩⟩
    exact hp ⟨actAny U a,actAny U b,⟨splitAction U s⟩⟩
  · rintro ⟨hn,hp⟩
    refine ⟨fun hz => hn ((action_zero_iff U f.2).mp hz),?_⟩
    rintro ⟨a,b,⟨s⟩⟩
    have back := splitAction U.symm s
    rw [actAny_inverse] at back
    exact hp ⟨actAny U.symm a,actAny U.symm b,⟨back⟩⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZFactors
end
