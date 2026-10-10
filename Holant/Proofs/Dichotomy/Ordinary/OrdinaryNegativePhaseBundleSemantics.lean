import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativePhaseBundleRaw

/-! Exact partition identity for the unsquared phase block compiler. The two
constant variables have exactly one supported assignment, while every original
declared variable, including unused ones, retains its two original choices. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativePhaseBundleSemantics
open Holant Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open OrdinaryNegativePhaseBundleRaw
open scoped BigOperators
namespace W
export StableHigherCurrentOrdinarySquare (rowValue weight extend value)
end W
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {K : Type} [Field K] {n s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s) → Signature K (a i.val))

theorem literal_row {m : ℕ} (j : Fin s) (f : Signature K m)
    (h : (⟨a j.val,H j⟩ : AnySignature K)=⟨m,f⟩) (scope : List ℕ) (x : ℕ→Bool) :
    W.rowValue H (j.val,scope) x=f (fun k=>x (scope.getD k.val 0)) := by
  obtain ⟨ha,hf⟩ := Sigma.mk.inj h
  subst m
  cases hf
  simp only [W.rowValue,dite_eq_left j.isLt]

theorem weight_append (rows more : List Factor) (x : ℕ→Bool) :
    W.weight H (rows++more) x=W.weight H rows x*W.weight H more x := by
  simp only [W.weight,List.map_append,List.prod_append]

theorem shift_getD (scope : List ℕ) {m : ℕ} (hlen : scope.length=m) (k : Fin m) :
    (scope.map (·+2)).getD k.val 0=scope.getD k.val 0+2 := by
  have h : k.val<scope.length := hlen ▸ k.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ h]
  simp

theorem shifted_row {m : ℕ} (j : Fin s) (f : Signature K m)
    (h : (⟨a j.val,H j⟩ : AnySignature K)=⟨m,f⟩)
    (scope : List ℕ) (hlen : scope.length=m) (x : ℕ→Bool) :
    W.rowValue H (j.val,scope.map (·+2)) x=f (fun k=>x (scope.getD k.val 0+2)) := by
  rw [literal_row H j f h]
  congr 1
  funext k
  rw [shift_getD scope hlen k]

variable (j e p₀ p₁ : Fin s) (f : Signature K n)
variable (hj : (⟨a j.val,H j⟩ : AnySignature K)=⟨n,f⟩)
variable (he : (⟨a e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h₀ : (⟨a p₀.val,H p₀⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h₁ : (⟨a p₁.val,H p₁⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (ps : List (Fin n→Bool ⊕ Fin 3))

include hj in
theorem phase_row (scope : List ℕ) (p : Fin n→Bool ⊕ Fin 3)
    (x : ℕ→Bool) (h0 : x 0=false) (h1 : x 1=true) :
    W.rowValue H (j.val,List.ofFn (fun k=>address scope (p k))) x=
      f (T.substitute p (fun k=>x (scope.getD k.val 0+2))) := by
  rw [literal_row H j f hj]
  congr 1
  funext k
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt),List.getElem_ofFn]
  cases hp : p k with
  | inl b => cases b <;> simp [T.substitute,address,h0,h1,hp]
  | inr t => simp [T.substitute,address,hp]

include hj in
theorem phase_weight (scope : List ℕ) (x : ℕ→Bool) (h0 : x 0=false) (h1 : x 1=true) :
    W.weight H (phaseRows j.val ps scope) x=
      B.evaluate f ps (fun k=>x (scope.getD k.val 0+2)) := by
  unfold W.weight phaseRows B.evaluate
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p _
  exact phase_row H j f hj scope p x h0 h1

include h₀ h₁ in
theorem constant_weight (x : ℕ→Bool) (h0 : x 0=false) (h1 : x 1=true) :
    W.weight H (constantRows p₀.val p₁.val ps) x=1 := by
  unfold W.weight constantRows
  simp only [List.map_map,Function.comp_def]
  apply List.prod_eq_one
  intro z hz
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hz
  have hk2 := constant_lt_two ps k hk
  by_cases h : k=0
  · subst k
    simp only [ite_true]
    rw [literal_row H p₀ _ h₀]
    simp [Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin,h0]
  · have hk1 : k=1 := by omega
    subst k
    simp only [ite_false,one_ne_zero]
    rw [literal_row H p₁ _ h₁]
    simp [Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin,h1]

include h₀ h₁ in
theorem guards_weight (x : ℕ→Bool) : W.weight H (guards p₀.val p₁.val) x=
    if x 0=false ∧ x 1=true then 1 else 0 := by
  simp only [W.weight,guards,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rw [literal_row H p₀ _ h₀,literal_row H p₁ _ h₁]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin,h0,h1]

variable (c : K) (hc : ∀z : Fin 3→Bool,B.evaluate f ps z=c*OrdinaryNegativeCubicCore.cubic z)

include hj he h₀ h₁ hc in
theorem block_weight (row : Factor) (valid : row.1<4 ∧ row.2.length=sourceArity row.1)
    (x : ℕ→Bool) (h0 : x 0=false) (h1 : x 1=true) :
    W.weight H (block j.val e.val p₀.val p₁.val ps row) x=
      (if row.1=0 then c else 1)*W.rowValue (sourceRows (K:=K)) row (fun k=>x (k+2)) := by
  rcases row with ⟨i,scope⟩
  obtain ⟨hi,hlen⟩ := valid
  interval_cases i
  · simp only [block,ite_true]
    rw [weight_append,phase_weight H j f hj ps scope x h0 h1,
      constant_weight H p₀ p₁ h₀ h₁ ps x h0 h1,mul_one,hc]
    rfl
  · simp only [block,show ¬(1 : ℕ)=0 by decide,ite_false,ite_true,
      W.weight,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul]
    rw [shifted_row H e _ he scope hlen]
    change (Holant.EightVertex.ProductAnchor.equalityFour _)*
      (Holant.EightVertex.ProductAnchor.equalityFour _)=
      Holant.EightVertex.ProductAnchor.equalityFour _
    simp only [Holant.EightVertex.ProductAnchor.equalityFour]
    split_ifs <;> simp
  · simp only [block,show ¬(2 : ℕ)=0 by decide,show ¬(2 : ℕ)=1 by decide,
      ite_false,ite_true,W.weight,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul]
    rw [shifted_row H p₀ _ h₀ scope hlen]
    simp only [W.rowValue,sourceRows,dite_eq_left (show (2 : ℕ)<4 by decide)]
    simp only [Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin]
    split_ifs <;> simp
  · simp only [block,show ¬(3 : ℕ)=0 by decide,show ¬(3 : ℕ)=1 by decide,
      show ¬(3 : ℕ)=2 by decide,ite_false,W.weight,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul]
    rw [shifted_row H p₁ _ h₁ scope hlen]
    simp only [W.rowValue,sourceRows,dite_eq_left (show (3 : ℕ)<4 by decide)]
    simp only [Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin]
    split_ifs <;> simp

include hj he h₀ h₁ hc in
theorem blocks_weight (rows : List Factor)
    (valid : ∀row∈rows,row.1<4 ∧ row.2.length=sourceArity row.1)
    (x : ℕ→Bool) (h0 : x 0=false) (h1 : x 1=true) :
    W.weight H (rows.flatMap (block j.val e.val p₀.val p₁.val ps)) x=
      c^(rows.filter (fun row=>row.1=0)).length*
        W.weight (sourceRows (K:=K)) rows (fun k=>x (k+2)) := by
  induction rows with
  | nil => simp [W.weight]
  | cons row rows ih =>
      rw [List.flatMap_cons,weight_append,
        block_weight H j e p₀ p₁ f hj he h₀ h₁ ps c hc row (valid row (by simp)) x h0 h1,
        ih (fun r hr=>valid r (by simp [hr]))]
      by_cases hr : row.1=0 <;>
        simp [W.weight,hr,pow_succ] <;> ring

include hj he h₀ h₁ hc in
theorem raw_weight (r : Source) (x : ℕ→Bool) :
    W.weight H (raw j.val e.val p₀.val p₁.val ps r.val).factors x=
      if x 0=false ∧ x 1=true then
        c^(copies r.val)*W.weight (sourceRows (K:=K)) r.val.factors (fun k=>x (k+2)) else 0 := by
  rw [raw,weight_append,guards_weight H p₀ p₁ h₀ h₁]
  by_cases h : x 0=false ∧ x 1=true
  · simp only [ite_eq_left h,mul_one]
    exact blocks_weight H j e p₀ p₁ f hj he h₀ h₁ ps c hc r.val.factors
      (fun row hr=>⟨(r.property row hr).1,(r.property row hr).2.1⟩) x h.1 h.2
  · simp only [ite_eq_right h,mul_zero]

theorem sum_cons {m : ℕ} (H : (Fin (m+1)→Bool)→K) :
    (∑x,H x)=∑b : Bool,∑x : Fin m→Bool,H (Fin.cons b x) := by
  let : Fintype (Bool×(Fin m→Bool)) := @instFintypeProd _ _ Bool.fintype inferInstance
  rw [←(Fin.consEquiv (fun _ : Fin (m+1)=>Bool)).sum_comp,Fintype.sum_prod_type]
  rfl

theorem extend_cons2 {m : ℕ} (b d : Bool) (x : Fin m→Bool) (k : ℕ) :
    W.extend (Fin.cons b (Fin.cons d x)) (k+2)=W.extend x k := by
  by_cases h : k<m
  · simp only [W.extend,dite_eq_left h,dite_eq_left (show k+2<m+2 by omega)]
    rfl
  · simp only [W.extend,dite_eq_right h,dite_eq_right (show ¬k+2<m+2 by omega)]

include hj he h₀ h₁ hc in
theorem value (r : Source) :
    W.value H (raw j.val e.val p₀.val p₁.val ps r.val)=
      c^(copies r.val)*W.value (sourceRows (K:=K)) r.val := by
  unfold W.value
  change (∑x : Fin (r.val.variables+2)→Bool,
    W.weight H (raw j.val e.val p₀.val p₁.val ps r.val).factors (W.extend x))=_
  rw [sum_cons]
  simp_rw [sum_cons,raw_weight H j e p₀ p₁ f hj he h₀ h₁ ps c hc r]
  have hz (b d : Bool) (x : Fin r.val.variables→Bool) : W.extend (Fin.cons b (Fin.cons d x)) 0=b := by
    simp only [W.extend,dite_eq_left (show 0<r.val.variables+2 by omega)]
    rfl
  have ho (b d : Bool) (x : Fin r.val.variables→Bool) : W.extend (Fin.cons b (Fin.cons d x)) 1=d := by
    simp only [W.extend,dite_eq_left (show 1<r.val.variables+2 by omega)]
    rfl
  simp_rw [hz,ho,extend_cons2]
  simp [Finset.mul_sum]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativePhaseBundleSemantics
end
