import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsConnectivity
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsMap

/-! Actual cap-ratio normalization closes the full equal-products branch to
an equality anchor. Every correcting binary is an old-family native-X gadget;
all projective scalars are retained, and the original family stays in the one
returned anchor basis. No supplied I or order-of-ratio assumption is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsAnchor
open Holant Holant.Tractable Holant.Algebraic Holant.OpenNetworkComposition
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open scoped BigOperators
namespace C
export GeneralCancellationCapPin (antiTensor)
end C
namespace G
export StableDenseResidualGaugeCore (weighted Products)
end G
namespace A
export PaperTerminalBridgeEqualProductsAlgebra (same_squares_dense)
end A
namespace R
export PaperTerminalBridgeEqualProductsConnectivity (weighted_relatives)
end R
namespace M
export PaperTerminalBridgeEqualProductsMap (dense_iff even_iff products_iff)
end M
namespace RH
export RingHomRealization (mapSignature mapFamily realizes_map)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

def attach (f : Signature K 4) (B : Fin 4→Signature K 2) : Signature K 4 :=
  spliceTensor (spliceTensor (spliceTensor (spliceTensor f (B 0) 0) (B 1) 1) (B 2) 2) (B 3) 3

theorem attach_actual (F : SignatureFamily K) (f : Signature K 4) (B : Fin 4→Signature K 2)
    (actual : Gadget.Realizes F .disequality f) (binaries : ∀i,Gadget.Realizes F .disequality (B i)) :
    Gadget.Realizes F .disequality (attach f B) :=
  realizes_splice F _ _ (realizes_splice F _ _ (realizes_splice F _ _
    (realizes_splice F f (B 0) actual (binaries 0) 0) (binaries 1) 1) (binaries 2) 2) (binaries 3) 3

theorem splice_value (f : Signature K n) (c p q : K) (i : Fin n) :
    spliceTensor f (fun x=>c*C.antiTensor p q x) i=
      fun x=>c*(if x i then q else p)*f x := by
  funext x
  cases hi : x i <;>
    simp [spliceTensor,C.antiTensor,Signature.disequality,hi,
      Function.update_eq_self,mul_comm]
  all_goals rw [←hi,Function.update_eq_self]
  all_goals ring

theorem equalized (a : K) (u kappa : Fin 4→K) :
    attach (G.weighted a u) (fun i x=>kappa i*C.antiTensor (u i) (u 0) x)=
      G.weighted (a*∏i,kappa i*u i) (fun _=>u 0) := by
  funext x
  simp only [attach,splice_value]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [G.weighted,table,h0,h1,h2,h3,Fin.prod_univ_four] <;> ring

theorem weighted_anchor (F : SignatureFamily AlgebraicComplex) (a : AlgebraicComplex)
    (u : Fin 4→AlgebraicComplex) (scale : a≠0) (live : ∀i,u i≠0)
    (actual : Gadget.Realizes F .disequality (G.weighted a u)) :
    Holant.EightVertex.ProductAnchor.HasEqualityAnchor F := by
  classical
  by_cases same : ∀i,u i^2=u 0^2
  · exact Holant.EightVertex.ProductAnchor.dense_realizing_family_anchor _
      (A.same_squares_dense a u scale live same) F actual
  have ratios := R.weighted_relatives F a u scale live actual same
  choose kappa nonzero binaries using ratios
  have dressed := attach_actual F (G.weighted a u)
    (fun i x=>kappa i*C.antiTensor (u i) (u 0) x) actual binaries
  rw [equalized] at dressed
  have scalar : a*(∏i,kappa i*u i)≠0 := mul_ne_zero scale
    (Finset.prod_ne_zero_iff.mpr (fun i _=>mul_ne_zero (nonzero i) (live i)))
  exact Holant.EightVertex.ProductAnchor.dense_realizing_family_anchor _
    (A.same_squares_dense _ (fun _=>u 0) scalar (fun _=>live 0) (fun _=>rfl)) F dressed

variable [CharZero K]
theorem source (phi : K→+*AlgebraicComplex) (F : SignatureFamily K)
    (q : Signature K 4) (actual : Gadget.Realizes F .disequality q)
    (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q) (products : G.Products q) :
    Holant.EightVertex.ProductAnchor.HasEqualityAnchor (RH.mapFamily phi F) := by
  let mapped := RH.mapSignature phi q
  have mappedEven : EvenSupport mapped := (M.even_iff phi q).mpr even
  have mappedDense : StableDenseParityAlgebra.Dense mapped := (M.dense_iff phi q).mpr dense
  have mappedProducts : StableDenseResidualAlgebra.Products mapped := (M.products_iff phi q).mpr products
  obtain ⟨u,live,factor⟩ := StableDenseResidualGaugeExistence.algebraic_factor mapped mappedEven mappedProducts
    mappedDense.1 mappedDense.2.1 mappedDense.2.2.1 mappedDense.2.2.2.1 mappedDense.2.2.2.2.1
  have mappedActual := RH.realizes_map phi actual
  change Gadget.Realizes (RH.mapFamily phi F) .disequality mapped at mappedActual
  rw [factor] at mappedActual
  exact weighted_anchor _ _ u mappedDense.1 live mappedActual


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsAnchor
end
