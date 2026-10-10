import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsMiddle
import Holant.Proofs.Algorithms.RingHomDescent

/-! Actual same-field normalization under equality of the three middle
opposite products. Endpoint values remain arbitrary and nonzero. The result
records the real finite sign mask; no unavailable independent Z action is
silently used to erase it. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsMiddleNormalize
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness.EightVertexNonexception
open scoped BigOperators
namespace G
export StableDenseResidualGaugeCore (weighted)
end G
namespace M
export PaperTerminalBridgeEqualProductsMiddle (Products Form factor relatives)
end M
namespace A
export PaperTerminalBridgeEqualProductsAnchor (attach attach_actual splice_value equalized)
end A
namespace RH
export RingHomRealization (mapSignature mapFamily realizes_map)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K L : Type} [Field K] [Field L]

def sign (s x : Fin 4→Bool) : K := (-1)^(∑i : Fin 4,if s i && x i then 1 else 0 : ℕ)
def Signed (q : Signature K 4) : Prop :=
  ∃c : K,c≠0 ∧ ∃s : Fin 4→Bool,∀x,weight x=2→q x=c*sign s x

theorem sign_sq (s x : Fin 4→Bool) : (sign (K:=K) s x)^2=1 := by
  unfold sign
  rw [←pow_mul,Nat.mul_comm,pow_mul]
  norm_num

theorem map_sign (phi : K→+*L) (s x : Fin 4→Bool) : phi (sign s x)=sign s x := by
  simp only [sign,map_pow,map_neg,map_one]

theorem signed_descend (phi : K→+*L) (q : Signature K 4) (signed : Signed (RH.mapSignature phi q)) : Signed q := by
  obtain ⟨c,live,s,form⟩ := signed
  let w : Fin 4→Bool := ![false,false,true,true]
  let d : K := q w*sign s w
  have ds : phi d=c := by
    change phi (q w*sign s w)=c
    rw [map_mul,map_sign]
    have h:=form w (by decide)
    change phi (q w)=c*sign s w at h
    rw [h,mul_assoc,←pow_two,sign_sq,mul_one]
  refine ⟨d,(map_ne_zero phi).mp (by rwa [ds]),s,?_⟩
  intro x middle
  apply phi.injective
  rw [map_mul,ds,map_sign]
  exact form x middle

theorem same_signed (q : Signature AlgebraicComplex 4) (a : AlgebraicComplex)
    (u : Fin 4→AlgebraicComplex) (form : M.Form q a u) (scale : a≠0) (live : ∀i,u i≠0)
    (same : ∀i,u i^2=u 0^2) : Signed q := by
  obtain ⟨rho,r,hrho,hr,s,eqn⟩ := PaperTerminalBridgeEqualProductsAlgebra.same_squares_dense a u scale live same
  refine ⟨rho*r^2,mul_ne_zero hrho (pow_ne_zero 2 hr),s,?_⟩
  intro x middle
  rw [form x middle,eqn x]
  simp [middle,sign,Holant.EightVertex.ProductAnchor.bitSign]

theorem attached_form (q : Signature K 4) (a : K) (u kappa : Fin 4→K) (form : M.Form q a u) :
    M.Form (A.attach q (fun i x=>kappa i*Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCancellationCapPin.antiTensor (u i) (u 0) x))
      (a*∏i,kappa i*u i) (fun _=>u 0) := by
  intro x middle
  calc
    _=A.attach (G.weighted a u) (fun i x=>kappa i*Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCancellationCapPin.antiTensor (u i) (u 0) x) x := by
      simp only [A.attach,A.splice_value]
      rw [form x middle]
    _=_ := congrFun (A.equalized a u kappa) x

theorem attached_nonzero_iff (q : Signature K 4) (u kappa : Fin 4→K)
    (live : ∀i,u i≠0) (nonzero : ∀i,kappa i≠0) (x : Fin 4→Bool) :
    A.attach q (fun i x=>kappa i*Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCancellationCapPin.antiTensor (u i) (u 0) x) x≠0 ↔ q x≠0 := by
  simp only [A.attach,A.splice_value]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [h0,h1,h2,h3,live,nonzero]

theorem normalize (F : SignatureFamily AlgebraicComplex) (q : Signature AlgebraicComplex 4)
    (actual : Gadget.Realizes F .disequality q) (even : EvenSupport q)
    (dense : StableDenseParityAlgebra.Dense q) (products : M.Products q) :
    ∃g : Signature AlgebraicComplex 4,Gadget.Realizes F .disequality g ∧
      EvenSupport g ∧ StableDenseParityAlgebra.Dense g ∧ Signed g := by
  classical
  obtain ⟨u,live,form⟩ := M.factor q even dense products
  by_cases same : ∀i,u i^2=u 0^2
  · exact ⟨q,actual,even,dense,same_signed q _ u form dense.1 live same⟩
  have ratios := M.relatives F q (entries q).a u even form dense.1 live actual same
  choose kappa nonzero binaries using ratios
  let g := A.attach q (fun i x=>kappa i*Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralCancellationCapPin.antiTensor (u i) (u 0) x)
  have actualG : Gadget.Realizes F .disequality g := A.attach_actual F q _ actual binaries
  have formG := attached_form q (entries q).a u kappa form
  have scalar : (entries q).a*(∏i,kappa i*u i)≠0 := mul_ne_zero dense.1
    (Finset.prod_ne_zero_iff.mpr (fun i _=>mul_ne_zero (nonzero i) (live i)))
  refine ⟨g,actualG,?_,?_,same_signed g _ (fun _=>u 0) formG scalar (fun _=>live 0) (fun _=>rfl)⟩
  · intro x odd
    simp only [g,A.attach,A.splice_value,even x odd,mul_zero]
  · have nz := attached_nonzero_iff q u kappa live nonzero
    simpa only [StableDenseParityAlgebra.Dense,entries,g,nz] using dense

theorem source (phi : K→+*AlgebraicComplex) (F : SignatureFamily K) (q : Signature K 4)
    (actual : Gadget.Realizes F .disequality q) (even : EvenSupport q)
    (dense : StableDenseParityAlgebra.Dense q) (products : M.Products q) :
    ∃g : Signature K 4,Gadget.Realizes F .disequality g ∧
      EvenSupport g ∧ StableDenseParityAlgebra.Dense g ∧ Signed g := by
  have pe : EvenSupport (RH.mapSignature phi q) := (PaperTerminalBridgeEqualProductsMap.even_iff phi q).mpr even
  have pd : StableDenseParityAlgebra.Dense (RH.mapSignature phi q) := (PaperTerminalBridgeEqualProductsMap.dense_iff phi q).mpr dense
  have pp : M.Products (RH.mapSignature phi q) := by
    simpa only [M.Products,entries,RH.mapSignature,←map_mul,phi.injective.eq_iff] using products
  obtain ⟨g,ag,eg,dg,sg⟩ := normalize (RH.mapFamily phi F) (RH.mapSignature phi q)
    (RH.realizes_map phi actual) pe pd pp
  obtain ⟨N,uses,edges,eqn⟩ := ag
  let D := RingHomDescent.descendNetwork phi N uses
  have mapped : RH.mapSignature phi D.tensor=g := (RingHomDescent.descend_tensor phi N uses).trans eqn
  refine ⟨D.tensor,⟨D,RingHomDescent.descend_labels phi N uses,edges,rfl⟩,?_,?_,?_⟩
  · exact (PaperTerminalBridgeEqualProductsMap.even_iff phi D.tensor).mp (mapped.symm ▸ eg)
  · exact (PaperTerminalBridgeEqualProductsMap.dense_iff phi D.tensor).mp (mapped.symm ▸ dg)
  · exact signed_descend phi D.tensor (mapped.symm ▸ sg)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsMiddleNormalize
end
