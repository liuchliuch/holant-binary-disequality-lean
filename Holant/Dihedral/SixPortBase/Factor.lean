import Holant.Dihedral.SixPortBase.Sector
import Holant.Dihedral.CompatibleCoefficientLine.TensorFactor

/-! Exact tensor factors with original port bijections. Analytic factors in
this file are not asserted to be available gadgets. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.SectorRuling
open Holant.Dihedral.CompatibleCoefficientLine
set_option backward.isDefEq.respectTransparency false

 def HasFactor (h : Signature Scalar 6) : Prop :=
  (∃ p : (Fin 1 ⊕ Fin 5) ≃ Fin 6,∃ u : Signature Scalar 1,∃ v : Signature Scalar 5,
    u ≠ 0 ∧ v ≠ 0 ∧ h=Tensor.reindex p (Tensor.tensor u v)) ∨
  (∃ p : (Fin 2 ⊕ Fin 4) ≃ Fin 6,∃ u : Signature Scalar 2,∃ v : Signature Scalar 4,
    u ≠ 0 ∧ v ≠ 0 ∧ h=Tensor.reindex p (Tensor.tensor u v))

 def HasProperTensorFactor (h : Signature Scalar 6) : Prop :=
  ∃ k l : ℕ,0<k ∧ 0<l ∧ ∃ p : (Fin k ⊕ Fin l) ≃ Fin 6,
    ∃ u : Signature Scalar k,∃ v : Signature Scalar l,
      u ≠ 0 ∧ v ≠ 0 ∧ h=Tensor.reindex p (Tensor.tensor u v)

 def TensorPrime (h : Signature Scalar 6) : Prop := h ≠ 0 ∧ ¬ HasProperTensorFactor h

 theorem HasFactor.proper {h : Signature Scalar 6} (hh : HasFactor h) : HasProperTensorFactor h := by
  rcases hh with h1|h2
  · exact ⟨1,5,by decide,by decide,h1⟩
  · exact ⟨2,4,by decide,by decide,h2⟩

 theorem nonzero_factors {k l : ℕ} (p : (Fin k ⊕ Fin l) ≃ Fin 6)
    (h : Signature Scalar 6) (u : Signature Scalar k) (v : Signature Scalar l)
    (hn : h ≠ 0) (he : h=Tensor.reindex p (Tensor.tensor u v)) : u ≠ 0 ∧ v ≠ 0 := by
  constructor
  · intro hu
    apply hn
    rw [he,hu]
    funext x
    simp [Tensor.reindex,Tensor.tensor]
  · intro hv
    apply hn
    rw [he,hv]
    funext x
    simp [Tensor.reindex,Tensor.tensor]

 def edgeOrder (e f : Fin 2) (hef : e ≠ f) : Equiv.Perm (Fin 2) :=
  Equiv.ofBijective ![e,f] (by fin_cases e <;> fin_cases f <;> simp_all <;> decide)

 def residualOrder (p : Ports) (e f : Fin 2) (hef : e ≠ f) : Equiv.Perm (Fin 4) :=
  (pairPorts 1).symm.trans ((Equiv.prodCongr (edgeOrder e f hef) (Equiv.refl _)).trans p)

 theorem residualOrder_values (p : Ports) (e f : Fin 2) (hef : e ≠ f) :
    residualOrder p e f hef 0=p (e,false) ∧
    residualOrder p e f hef 1=p (e,true) ∧
    residualOrder p e f hef 2=p (f,false) ∧
    residualOrder p e f hef 3=p (f,true) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

 theorem residual_fixed_factor (h : Signature Scalar 6) (hn : h ≠ 0)
    (p : Ports) (e f : Fin 2) (hef : e ≠ f) (Q : Mat) (R : Signature Scalar 4)
    (he : ∀ a b y,h (pair a b y)=
      Q (y (p (e,false))) (y (p (e,true))) *
      R (pair a b ![y (p (f,false)),y (p (f,true))])) : HasFactor h := by
  let o := liftPair (residualOrder p e f hef)
  let h' := Tensor.reindex o.symm h
  have hh : ∀ a b c d x,h' (pair a b (pair c d x))=Q c d*R (pair a b x) := by
    intro a b c d x
    change h (fun i => pair a b (pair c d x) (o.symm i))=_
    rw [word_liftPair,he]
    have ho := residualOrder_values p e f hef
    have h0 : (residualOrder p e f hef).symm (p (e,false))=0 := by rw [←ho.1]; exact Equiv.symm_apply_apply _ _
    have h1 : (residualOrder p e f hef).symm (p (e,true))=1 := by rw [←ho.2.1]; exact Equiv.symm_apply_apply _ _
    have h2 : (residualOrder p e f hef).symm (p (f,false))=2 := by rw [←ho.2.2.1]; exact Equiv.symm_apply_apply _ _
    have h3 : (residualOrder p e f hef).symm (p (f,true))=3 := by rw [←ho.2.2.2]; exact Equiv.symm_apply_apply _ _
    simp only [h0,h1,h2,h3,pair,Fin.cons_zero,Fin.cons_succ]
    congr 2
    funext i
    fin_cases i <;> rfl
  have hf := tensor_factor_of_slices h' Q R hh
  have hfinal : h=Tensor.reindex ((factorPorts 2).trans o) (Tensor.tensor (Tractable.kernelSignature Q) R) := by
    have hh := congrArg (Tensor.reindex o) hf
    simpa only [h',Tensor.reindex_trans,Equiv.symm_trans_self,Tensor.reindex_refl] using hh
  exact Or.inr ⟨_,_,_,(nonzero_factors _ h _ _ hn hfinal).1,
    (nonzero_factors _ h _ _ hn hfinal).2,hfinal⟩

/-- If the opposite parity sector vanishes, the exact common factor supplied
by the surviving ruling factors from the entire original six-port tensor. -/
 theorem factor_of_zero_sector {m : ℕ} (h : Signature Scalar 6) (hn : h ≠ 0)
    (γ : Bool) (D : ExactPencil m (sectorFirst (s:=2) h γ) (sectorSecond (s:=2) h γ))
    (hz : sectorFirst (s:=2) h (!γ)=0 ∧ sectorSecond (s:=2) h (!γ)=0) : HasFactor h := by
  let R : Signature Scalar 4 := fun x =>
    if x 1=(x 0 ^^ γ) then (if x 0 then D.second else D.first) (x 2) (x 3) else 0
  apply residual_fixed_factor h hn D.ports D.fixedEdge D.varyingEdge D.distinct D.fixed R
  intro a b y
  have hU := congrFun D.first_exact y
  have hV := congrFun D.second_exact y
  have hzU := congrFun hz.1 y
  have hzV := congrFun hz.2 y
  cases γ <;> cases a <;> cases b
  all_goals first
    | simpa [R,sectorFirst,sectorSecond,twoProduct,pair] using hU
    | simpa [R,sectorFirst,sectorSecond,twoProduct,pair] using hV
    | simpa [R,sectorFirst,sectorSecond,twoProduct,pair] using hzU
    | simpa [R,sectorFirst,sectorSecond,twoProduct,pair] using hzV

end Holant.Dihedral.SixPortBase
