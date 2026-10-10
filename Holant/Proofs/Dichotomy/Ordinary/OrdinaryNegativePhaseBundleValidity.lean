import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativePhaseBundleRaw

/-! Occurrence parity of the actual emitted phase instance, with source
variableCount shifted by two and every constant port balanced by its own pin. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativePhaseBundleValidity
open Holant Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open OrdinaryNegativePhaseBundleRaw
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences
  (rawPorts occurrences address constantAddresses even_address_counts)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {n s : ℕ} {a : ℕ→ℕ}
variable (j e p₀ p₁ : Fin s) (ps : List (Fin n→Bool ⊕ Fin 3))
variable (hj : a j.val=n) (he : a e.val=4) (h₀ : a p₀.val=1) (h₁ : a p₁.val=1)

def Good (variableCount : ℕ) (row : Factor) : Prop :=
  row.1<s ∧ row.2.length=a row.1 ∧ ∀k∈row.2,k<variableCount

include hj in
theorem phase_good (r : Source) (scope : List ℕ) (hlen : scope.length=3)
    (hscope : ∀k∈scope,k<r.val.variables) (p : Fin n→Bool ⊕ Fin 3) :
    Good (s:=s) (a:=a) (r.val.variables+2)
      (j.val,List.ofFn (fun k=>OrdinaryNegativePhaseBundleRaw.address scope (p k))) := by
  refine ⟨j.isLt,by simp [hj],?_⟩
  intro z hz
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hz
  cases hp : p k with
  | inl b => cases b <;> simp [OrdinaryNegativePhaseBundleRaw.address]
  | inr t =>
      have ht : t.val<scope.length := by rw [hlen]; exact t.isLt
      have hg := hscope (scope.getD t.val 0) (by
        rw [List.getD_eq_getElem _ _ ht]
        exact List.getElem_mem ht)
      simp only [OrdinaryNegativePhaseBundleRaw.address]
      omega

include h₀ h₁ in
theorem constant_good (variableCount : ℕ) (k : ℕ) (hk : k<2) :
    Good (s:=s) (a:=a) (variableCount+2) (if k=0 then p₀.val else p₁.val,[k]) := by
  by_cases h : k=0
  · simp only [h,ite_true]
    refine ⟨p₀.isLt,by simpa using h₀.symm,?_⟩
    intro z hz
    have hz0 : z=0 := by simpa using hz
    omega
  · simp only [h,ite_false]
    refine ⟨p₁.isLt,by simpa using h₁.symm,?_⟩
    intro z hz
    have hz' : z=k := by simpa using hz
    omega

theorem shifted_good (r : Source) (scope : List ℕ) (label : Fin s)
    (hlen : scope.length=a label.val) (hscope : ∀k∈scope,k<r.val.variables) :
    Good (s:=s) (a:=a) (r.val.variables+2) (label.val,scope.map (·+2)) := by
  refine ⟨label.isLt,by simpa using hlen,?_⟩
  intro z hz
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hz
  have h := hscope k hk
  omega

include hj he h₀ h₁ in
theorem block_good (r : Source) (row : Factor) (hr : row∈r.val.factors) :
    ∀target∈block j.val e.val p₀.val p₁.val ps row,
      Good (s:=s) (a:=a) (r.val.variables+2) target := by
  obtain ⟨hlabel,hlen,hscope⟩ := r.property row hr
  intro target ht
  by_cases hz : row.1=0
  · simp only [block,hz,ite_true,List.mem_append] at ht
    rcases ht with ht|ht
    · obtain ⟨p,_,rfl⟩ := List.mem_map.mp ht
      apply phase_good j hj r row.2
      · simpa only [hz,sourceArity] using hlen
      · exact hscope
    · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ht
      exact constant_good p₀ p₁ h₀ h₁ r.val.variables k (constant_lt_two ps k hk)
  · have targets : target=(if row.1=1 then e.val else if row.1=2 then p₀.val else p₁.val,
        row.2.map (·+2)) := by simpa [block,hz] using ht
    rw [targets]
    by_cases h1 : row.1=1
    · simp only [h1,ite_true]
      exact shifted_good r row.2 e (by simpa [h1,sourceArity,he] using hlen) hscope
    · by_cases h2 : row.1=2
      · simp only [h2,ite_true]
        exact shifted_good r row.2 p₀ (by simpa [h2,sourceArity,h₀] using hlen) hscope
      · have h3 : row.1=3 := by omega
        simp only [h1,h2,ite_false]
        exact shifted_good r row.2 p₁ (by simpa [h3,sourceArity,h₁] using hlen) hscope

include h₀ h₁ in
theorem guards_good (variableCount : ℕ) :
    ∀row∈guards p₀.val p₁.val,Good (s:=s) (a:=a) (variableCount+2) row := by
  intro row hr
  simp only [guards,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact constant_good p₀ p₁ h₀ h₁ variableCount 0 (by decide)
  · exact constant_good p₀ p₁ h₀ h₁ variableCount 0 (by decide)
  · simpa using constant_good p₀ p₁ h₀ h₁ variableCount 1 (by decide)
  · simpa using constant_good p₀ p₁ h₀ h₁ variableCount 1 (by decide)

theorem constants_match : OrdinaryNegativePhaseBundleRaw.constantAddresses ps=O.constantAddresses ps := by
  unfold OrdinaryNegativePhaseBundleRaw.constantAddresses O.constantAddresses
  congr 1
  funext p
  cases p with
  | inl b => cases b <;> rfl
  | inr k => rfl

theorem address_match (scope : List ℕ) : OrdinaryNegativePhaseBundleRaw.address scope=
    O.address (fun k : Fin 3=>scope.getD k.val 0) := by
  funext p
  cases p with
  | inl b => cases b <;> rfl
  | inr k => rfl

variable (even : ∀k : Fin 3,Even (O.occurrences ps k))

include even in
theorem block_even (row : Factor) (i : ℕ) :
    Even (((block j.val e.val p₀.val p₁.val ps row).flatMap Prod.snd).count i) := by
  by_cases h : row.1=0
  · simp only [block,h,ite_true,List.flatMap_append,phase_addresses,constant_addresses]
    rw [constants_match,address_match]
    exact O.even_address_counts ps (fun k : Fin 3=>row.2.getD k.val 0) even i
  · simp only [block,h,ite_false,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.count_append]
    exact ⟨_,rfl⟩

theorem guards_even (i : ℕ) : Even (((guards p₀.val p₁.val).flatMap Prod.snd).count i) := by
  simp only [guards,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.cons_append,
    List.nil_append,List.count_cons,List.count_nil]
  split_ifs <;> decide

include even in
theorem raw_even (r : Raw) (i : ℕ) :
    Even ((raw j.val e.val p₀.val p₁.val ps r).degree i) := by
  rw [StableHigherCurrentOrdinarySquare.degree_flat]
  simp only [raw,List.flatMap_append,List.count_append]
  apply Even.add _ (guards_even p₀ p₁ i)
  have h (rs : List Factor) : Even (((rs.flatMap (block j.val e.val p₀.val p₁.val ps)).flatMap Prod.snd).count i) := by
    induction rs with
    | nil => simp
    | cons row rs ih =>
        simp only [List.flatMap_cons,List.flatMap_append,List.count_append]
        exact (block_even j e p₀ p₁ ps even row i).add ih
  exact h r.factors

include hj he h₀ h₁ even in
theorem raw_valid (r : Source) : (raw j.val e.val p₀.val p₁.val ps r.val).Valid s a := by
  have hgood : ∀row∈(raw j.val e.val p₀.val p₁.val ps r.val).factors,
      Good (s:=s) (a:=a) (r.val.variables+2) row := by
    intro row hr
    rcases List.mem_append.mp hr with hr|hr
    · obtain ⟨old,ho,hr⟩ := List.mem_flatMap.mp hr
      exact block_good j e p₀ p₁ ps hj he h₀ h₁ r old ho row hr
    · exact guards_good p₀ p₁ h₀ h₁ r.val.variables row hr
  refine ⟨?_,?_,fun i _=>raw_even j e p₀ p₁ ps even r.val i⟩
  · intro v
    exact ⟨(hgood _ (List.get_mem _ v)).1,(hgood _ (List.get_mem _ v)).2.1⟩
  · intro p
    exact (hgood _ (List.get_mem _ p.1)).2.2 _ (List.get_mem _ p.2)

def query (r : Source) : Raw.Input s a :=
  ⟨raw j.val e.val p₀.val p₁.val ps r.val,raw_valid j e p₀ p₁ ps hj he h₀ h₁ even r⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativePhaseBundleValidity
end
