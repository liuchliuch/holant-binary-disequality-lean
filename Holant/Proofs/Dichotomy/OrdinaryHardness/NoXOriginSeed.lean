import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginNormalizationGraph

/-! Two retained zero-pin boundary vertices give every selected bad local
twist an actual graph of arity at least two, including unary input rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginSeed
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open scoped BigOperators
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (tensor tensor_denote)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {arity : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (arity i.val)}

def extend (x : Word n) : Word (n+2) := Fin.addCases x (fun _ : Fin 2=>false)

theorem extend_affine : TwoTranslate.IsAffineMap (extend (n:=n)) := by
  intro x y
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [extend,AffinePhase.xor,AffinePhase.origin]
  · intro j
    simp [extend,AffinePhase.xor,AffinePhase.origin]

def padded (N : M.Macro H n) (P : M.Macro H 1) : M.Macro H (n+2) := N.tensor (P.tensor P)

theorem padded_value (N : M.Macro H n) (P : M.Macro H 1)
    (pin : P.network.denote=fun x=>if x 0=false then 1 else 0) (x : Word n) :
    (padded N P).network.denote (extend x)=N.network.denote x := by
  rw [padded,M.tensor_denote,M.tensor_denote]
  simp [Signature.tensor_apply,extend,pin]

theorem twisted_value (phi : K→+*AlgebraicComplex) (N : M.Macro H n) (P : M.Macro H 1)
    (pin : P.network.denote=fun x=>if x 0=false then 1 else 0) (a x : Word n) :
    localTwist (extend a) (fun y=>phi ((padded N P).network.denote y)) (extend x)=
      localTwist a (fun y=>phi (N.network.denote y)) x := by
  rw [localTwist_apply,localTwist_apply,padded_value N P pin]
  congr 1
  rw [Fin.prod_univ_add]
  simp [extend]

theorem bad_padded (phi : K→+*AlgebraicComplex) (N : M.Macro H n) (P : M.Macro H 1)
    (pin : P.network.denote=fun x=>if x 0=false then 1 else 0)
    (bad : ¬LocalAffine (fun x=>phi (N.network.denote x))) :
    ∃a : Word (n+2),phi ((padded N P).network.denote a)≠0 ∧
      ¬Affine (localTwist a (fun x=>phi ((padded N P).network.denote x))) := by
  classical
  obtain ⟨a,supported,negative⟩ : ∃a,∃_ : phi (N.network.denote a)≠0,
      ¬Affine (localTwist a (fun x=>phi (N.network.denote x))) := by
    simpa only [LocalAffine,not_forall,not_imp] using bad
  refine ⟨extend a,?_,?_⟩
  · rwa [padded_value N P pin]
  · intro good
    apply negative
    have h := good.precompose extend extend_affine
    convert h using 1
    funext x
    exact (twisted_value phi N P pin a x).symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginSeed
end
