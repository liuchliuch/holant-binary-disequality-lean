import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsAnchor

/-! Middle-product normalization with independent endpoint coefficients.
Only the six weight-two entries enter the cap identities; endpoint completion
is semantic factorization data and is never added as a physical vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsMiddle
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace G
export StableDenseResidualGaugeCore (weighted Products)
end G
namespace C
export GeneralCancellationCapPin (network coefficients oriented full_table antiTensor)
export EightVertexGaugeCaps (weighted_even exact_cap scalar loopPorts remainingPorts)
end C
namespace R
export PaperTerminalBridgeEqualProductsCaps (Rel cap_actual unscale)
export PaperTerminalBridgeEqualProductsConnectivity (relatives_of_caps)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def Products (q : Signature K 4) : Prop :=
  (entries q).b*(entries q).y=(entries q).d*(entries q).w ∧
  (entries q).c*(entries q).z=(entries q).d*(entries q).w

def Form (q : Signature K 4) (a : K) (u : Fin 4→K) : Prop :=
  ∀x,weight x=2→q x=G.weighted a u x

def completion (q : Signature K 4) : Signature K 4 :=
  let p:=entries q
  table ⟨p.a,p.b,p.c,p.d,p.w,p.z,p.y,p.b*p.y/p.a⟩

theorem completion_even (q : Signature K 4) : EvenSupport (completion q) := by
  intro x odd
  have hw := Holant.EightVertex.ProductAnchor.weight_four x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [h0,h1,h2,h3] at hw
  all_goals first | (exact (odd (by omega)).elim) | simp [completion,table,h0,h1,h2,h3]

theorem completion_products (q : Signature K 4) (scale : (entries q).a≠0) (products : Products q) :
    G.Products (completion q) := by
  have first : (entries q).a*((entries q).b*(entries q).y/(entries q).a)=(entries q).b*(entries q).y := by
    field_simp
  refine ⟨first,?_,?_⟩
  · change (entries q).a*((entries q).b*(entries q).y/(entries q).a)=(entries q).c*(entries q).z
    rw [first]
    exact products.1.trans products.2.symm
  · change (entries q).a*((entries q).b*(entries q).y/(entries q).a)=(entries q).d*(entries q).w
    rw [first]
    exact products.1

theorem completion_middle (q : Signature K 4) (even : EvenSupport q) (x : Fin 4→Bool)
    (middle : weight x=2) : q x=completion q x := by
  rw [←table_entries q even]
  have hw := Holant.EightVertex.ProductAnchor.weight_four x
  rw [middle] at hw
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [h0,h1,h2,h3] at hw
  all_goals simp [completion,table,entries,h0,h1,h2,h3]

theorem factor (q : Signature AlgebraicComplex 4) (even : EvenSupport q)
    (dense : StableDenseParityAlgebra.Dense q) (products : Products q) :
    ∃u : Fin 4→AlgebraicComplex,(∀i,u i≠0) ∧ Form q (entries q).a u := by
  have completed : StableDenseResidualAlgebra.Products (completion q) := completion_products q dense.1 products
  obtain ⟨u,live,equation⟩ := StableDenseResidualGaugeExistence.algebraic_factor (completion q)
    (completion_even q) completed dense.1 dense.2.1 dense.2.2.1 dense.2.2.2.1 dense.2.2.2.2.1
  refine ⟨u,live,?_⟩
  intro x middle
  rw [completion_middle q even x middle,equation]
  rfl

theorem reindex_form (q : Signature K 4) (a : K) (u : Fin 4→K) (form : Form q a u)
    (e : Equiv.Perm (Fin 4)) : Form (Tensor.reindex e q) a (fun i=>u (e.symm i)) := by
  intro x middle
  have hw : weight (fun i=>x (e i))=weight x := Equiv.sum_comp e (fun i=>if x i then 1 else 0)
  change q (fun i=>x (e i))=_
  rw [form _ (hw.trans middle)]
  exact congrFun (EightVertexGaugePorts.weighted_reindex a u e) x

theorem reindex_even (q : Signature K 4) (even : EvenSupport q) (e : Equiv.Perm (Fin 4)) :
    EvenSupport (Tensor.reindex e q) := by
  intro x odd
  apply even
  have hw : weight (fun i=>x (e i))=weight x := Equiv.sum_comp e (fun i=>if x i then 1 else 0)
  rwa [hw]

theorem coefficients (q : Signature K 4) (a : K) (u : Fin 4→K) (form : Form q a u) (k : Fin 6) :
    C.coefficients q k=C.coefficients (G.weighted a u) k := by
  have b:=form ![false,false,true,true] (by decide)
  have c:=form ![false,true,false,true] (by decide)
  have d:=form ![false,true,true,false] (by decide)
  have w:=form ![true,false,false,true] (by decide)
  have z:=form ![true,false,true,false] (by decide)
  have y:=form ![true,true,false,false] (by decide)
  simp only [C.coefficients,entries,b,c,d,w,z,y]

variable [CharZero K]
theorem cap_relation (F : SignatureFamily K) (q : Signature K 4) (a : K) (u : Fin 4→K)
    (even : EvenSupport q) (form : Form q a u) (scale : a≠0)
    (actual : Gadget.Realizes F .disequality q) (k : Fin 6)
    (sum : u (C.loopPorts k).1+u (C.loopPorts k).2≠0) :
    R.Rel F (u (C.remainingPorts k).1) (u (C.remainingPorts k).2) := by
  have h := R.cap_actual F q actual (k,true)
  have eqn : (C.network q (k,true)).denote=(C.network (G.weighted a u) (k,true)).denote := by
    rw [C.full_table q even,C.full_table _ (C.weighted_even a u)]
    simp only [C.oriented,coefficients q a u form]
  rw [eqn,C.exact_cap] at h
  exact R.unscale F _ (C.scalar a u k) (mul_ne_zero scale sum) h

theorem relatives (F : SignatureFamily K) (q : Signature K 4) (a : K) (u : Fin 4→K)
    (even : EvenSupport q) (form : Form q a u) (scale : a≠0) (live : ∀i,u i≠0)
    (actual : Gadget.Realizes F .disequality q) (different : ¬∀i,u i^2=u 0^2) :
    ∀i,R.Rel F (u i) (u 0) := by
  apply R.relatives_of_caps F u live different
  intro e k sum
  have moved := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality q actual e.symm
  simp only [Equiv.symm_symm] at moved
  exact cap_relation F (Tensor.reindex e q) a (fun i=>u (e.symm i))
    (reindex_even q even e) (reindex_form q a u form e) scale moved k sum


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsMiddle
end
