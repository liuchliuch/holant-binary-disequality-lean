import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCapSelection
import Holant.Tractable.SymmetricBinaryPullback.Basic

/-! The physical regular-cap selector consumes the actual GHZ decomposition
in an ambient algebraic field. All selected graphs and coefficients remain
in the original source field, even when the decomposition matrix does not. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZCapProducer
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain OrdinaryNegativeCubicGadgets
namespace C
export GlobalCloseCompletionSymmetricGHZCapGraph (symmetric cap)
export GlobalCloseCompletionSymmetricGHZCapSelection (matrix Semisimple select)
end C
namespace A
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz ghz_value)
export GlobalCloseCompletionSymmetricGHZRegularCap (hyperdet ghz_hyperdet)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]
variable (phi : K→+*AlgebraicComplex) (f : Signature K 3) (R : InvertibleKernel)
variable (form : RingHomRealization.mapSignature phi f=A.ghz R.matrix)

def a : K:=f ![false,false,false]
def b : K:=f ![false,false,true]
def c : K:=f ![false,true,true]
def d : K:=f ![true,true,true]

include form in
theorem form_symmetric : f=C.symmetric (a f) (b f) (c f) (d f) := by
  funext x
  apply phi.injective
  have value (y : Fin 3→Bool) : phi (f y)=A.ghz R.matrix y:=congrFun form y
  rw [value]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp only [C.symmetric,h0,h1,h2,Bool.false_eq_true,ite_false,ite_true,a,b,c,d,value]
  all_goals simp [A.ghz_value,h0,h1,h2] <;> ring

include form in
theorem hyperdet_nonzero : A.hyperdet (a f) (b f) (c f) (d f)≠0 := by
  intro zero
  have live := pow_ne_zero 6 (SymmetricBinaryPullback.determinant_ne_zero R)
  apply live
  have h:=congrArg phi zero
  have value (y : Fin 3→Bool) : phi (f y)=A.ghz R.matrix y:=congrFun form y
  simp only [A.hyperdet,map_sub,map_pow,map_mul,map_ofNat,map_zero,a,b,c,d,value] at h
  have identity:=A.ghz_hyperdet R.matrix
  unfold A.hyperdet at identity
  exact identity.symm.trans h

variable {r : ℕ} {arity : ℕ→ℕ} {H : (i : Fin r)→Signature K (arity i.val)}

theorem produce (N : Macro H 3) (P : Bool→Macro H 1)
    (R : InvertibleKernel) (form : RingHomRealization.mapSignature phi N.network.denote=A.ghz R.matrix)
    (pins : ∀v,(P v).network.denote=QuaternaryUnaryAccess.pin v) :
    (∃a d : K,a≠0 ∧ d≠0 ∧ N.network.denote=C.symmetric a 0 0 d) ∨
      ∃U : Macro H 1,Matrix.det (C.matrix (C.cap N U))≠0 ∧ C.Semisimple (C.matrix (C.cap N U)) := by
  have shape:=form_symmetric phi N.network.denote R form
  rcases C.select N P (a N.network.denote) (b N.network.denote) (c N.network.denote) (d N.network.denote)
    shape (hyperdet_nonzero phi N.network.denote R form) pins with ⟨hb,hc,ha,hd⟩|good
  · exact Or.inl ⟨a N.network.denote,d N.network.denote,ha,hd,by simpa only [hb,hc] using shape⟩
  · exact Or.inr good

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZCapProducer
end
