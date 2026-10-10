import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNANDMinorRaw

/-! Exact binary-minor semantics: both appended constants have one supported
assignment, and all original declared variables retain their original choices. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDMinorSemantics
open Holant Holant.Complexity
open OrdinaryNegativeNANDMinorRaw
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace W
export StableHigherCurrentOrdinarySquare (rowValue weight extend value)
end W
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace V
export BinaryCSPProgrammeValue (value weight assignment)
end V
namespace Gates
export Holant.LocalDrafts.RemoteWork.CountingBridge.Gates (pin)
end Gates
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [CommSemiring K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))

theorem literal_row {m : ℕ} (j : Fin s) (f : Signature K m)
    (h : (⟨a j.val,H j⟩ : AnySignature K)=⟨m,f⟩) (scope : List ℕ) (x : ℕ→Bool) :
    W.rowValue H (j.val,scope) x=f (fun k=>x (scope.getD k.val 0)) := by
  obtain ⟨ha,hf⟩ := Sigma.mk.inj h
  subst m
  cases hf
  simp only [W.rowValue,dite_eq_left j.isLt]

variable (j p₀ p₁ : Fin s) (q : Fin (a j.val)→Bool ⊕ Fin 2)
variable (h₀ : (⟨a p₀.val,H p₀⟩ : AnySignature K)=⟨1,Gates.pin false⟩)
variable (h₁ : (⟨a p₁.val,H p₁⟩ : AnySignature K)=⟨1,Gates.pin true⟩)

def minor : Signature K 2 := fun z=>H j (T.substitute q z)

theorem selected_row (v : ℕ) (e : ℕ×ℕ) (x : ℕ→Bool)
    (h0 : x v=false) (h1 : x (v+1)=true) :
    W.rowValue H (row j.val q v e) x=minor H j q ![x e.1,x e.2] := by
  rw [row,literal_row H j (H j) rfl]
  congr 1
  funext k
  rw [List.getD_eq_getElem _ _ (by simpa using k.isLt),List.getElem_ofFn]
  cases hp : q k with
  | inl b => cases b <;> simp [T.substitute,address,h0,h1,hp]
  | inr t => fin_cases t <;> simp [T.substitute,address,hp]

include h₀ h₁ in
theorem raw_weight (r : C.Raw) (x : ℕ→Bool) :
    W.weight H (raw j.val p₀.val p₁.val q r).factors x=
      if x r.variables=false ∧ x (r.variables+1)=true then
        (r.edges.map (fun e=>minor H j q ![x e.1,x e.2])).prod else 0 := by
  simp only [W.weight,raw,List.map_cons,List.prod_cons]
  rw [literal_row H p₀ _ h₀,literal_row H p₁ _ h₁]
  by_cases h : x r.variables=false ∧ x (r.variables+1)=true
  · simp only [Gates.pin,Fin.val_zero,List.getD_cons_zero,h.1,h.2,ite_true,and_self,one_mul,List.map_map]
    congr 1
    apply List.map_congr_left
    intro e _
    exact selected_row H j q r.variables e x h.1 h.2
  · cases h0 : x r.variables <;> cases h1 : x (r.variables+1) <;>
      simp [Gates.pin,h0,h1] at h ⊢

theorem sum_append {m n : ℕ} (f : (Fin (m+n)→Bool)→K) :
    (∑z,f z)=∑x : Fin m→Bool,∑y : Fin n→Bool,f (Fin.append x y) := by
  rw [←(Fin.appendEquiv m n).sum_comp,Fintype.sum_prod_type]
  rfl

theorem sum_two (f : (Fin 2→Bool)→K) :
    (∑z,f z)=∑b : Bool,∑c : Bool,f ![b,c] := by
  rw [←(finTwoArrowEquiv Bool).symm.sum_comp,Fintype.sum_prod_type]
  rfl

theorem extend_append_old {m n : ℕ} (x : Fin m→Bool) (y : Fin n→Bool)
    (k : ℕ) (hk : k<m) : W.extend (Fin.append x y) k=W.extend x k := by
  simp only [W.extend,dite_eq_left hk,dite_eq_left (show k<m+n by omega)]
  exact Fin.append_left x y ⟨k,hk⟩

theorem extend_append_new {m n : ℕ} (x : Fin m→Bool) (y : Fin n→Bool)
    (k : Fin n) : W.extend (Fin.append x y) (m+k.val)=y k := by
  rw [W.extend,dite_eq_left (show m+k.val<m+n by omega)]
  exact Fin.append_right x y k

include h₀ h₁ in
theorem query_value (r : P.Input) :
    W.value H (query j p₀ p₁ q (congrArg Sigma.fst h₀) (congrArg Sigma.fst h₁) r).val=
      V.value (fun b c=>minor H j q ![b,c]) r.val := by
  unfold W.value
  change (∑z : Fin (r.val.variables+2)→Bool,
    W.weight H (raw j.val p₀.val p₁.val q r.val).factors (W.extend z))=_
  rw [sum_append]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [sum_two,raw_weight H j p₀ p₁ q h₀ h₁]
  simp only [Fintype.sum_bool]
  have hz (b c : Bool) : W.extend (Fin.append x ![b,c]) r.val.variables=b := by
    simpa using extend_append_new x ![b,c] (0 : Fin 2)
  have ho (b c : Bool) : W.extend (Fin.append x ![b,c]) (r.val.variables+1)=c := by
    simpa using extend_append_new x ![b,c] (1 : Fin 2)
  simp only [hz,ho,Bool.false_eq_true,Bool.true_eq_false,and_self,ite_false,ite_true,
    true_and,false_and,zero_add,add_zero]
  unfold V.weight
  congr 1
  apply List.map_congr_left
  intro e he
  have hb := r.property.1 e he
  rw [extend_append_old x ![false,true] e.1 hb.1,
    extend_append_old x ![false,true] e.2 hb.2]
  simp only [OrdinaryNegativeNANDTable.assignment_eq]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDMinorSemantics
end
