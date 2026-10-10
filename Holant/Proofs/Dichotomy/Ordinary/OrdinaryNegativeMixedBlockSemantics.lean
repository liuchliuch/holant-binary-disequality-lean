import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockData

/-! Exact ordinary partition semantics of heterogeneous literal row blocks.
Four actual target pins fix exactly the two reserved constant variables; the
complete original free-variable sum, including unused variables, is retained.
Pairings enter only through canonical arity metadata. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockSemantics
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
namespace D
export OrdinaryNegativeMixedBlockData (family Recipe Input raw factor guards coefficient)
end D
namespace C
export GeneralEOPairedCSPFamilyRaw (Raw value)
end C
namespace B
export GeneralEOPairedFamilyBundleRaw (data query)
export GeneralEOPairedFamilyBundleValue (data_length query_value)
end B
namespace W
export StableHigherCurrentOrdinarySquare (rowValue weight extend value)
end W
namespace F
export GeneralEOPairedFamilyExtractionWriter (weight weight_cons weight_nil)
end F
namespace Pn
export GeneralEOPairedFamilyExtractionPinRaw (weight fixed anchor read_anchor sum_cons)
end Pn
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

variable {K : Type} [CommSemiring K] {u s : ℕ} {a b : ℕ → ℕ}
variable (H : (j : Fin s) → Signature K (b j.val))
variable (recipe : D.Recipe (u:=u) (s:=s) (a:=a) (b:=b))
variable (p₀ p₁ : Fin s)
variable (h₀ : (⟨b p₀.val,H p₀⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h₁ : (⟨b p₁.val,H p₁⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)

theorem literal_row {m : ℕ} (j : Fin s) (f : Signature K m)
    (h : (⟨b j.val,H j⟩ : AnySignature K)=⟨m,f⟩) (scope : List ℕ) (x : ℕ → Bool) :
    W.rowValue H (j.val,scope) x=f (fun k => x (scope.getD k.val 0)) := by
  obtain ⟨ha,hf⟩ := Sigma.mk.inj h
  subst m
  cases hf
  simp only [W.rowValue,dite_eq_left j.isLt]

theorem weight_append (rows more : List Factor) (x : ℕ → Bool) :
    W.weight H (rows++more) x=W.weight H rows x*W.weight H more x := by
  simp only [W.weight,List.map_append,List.prod_append]

include h₀ h₁ in
theorem guards_weight (x : ℕ → Bool) : W.weight H (D.guards p₀ p₁) x=
    if x 0=false ∧ x 1=true then 1 else 0 := by
  simp only [W.weight,D.guards,OrdinaryNegativePhaseBundleRaw.guards,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rw [literal_row H p₀ _ h₀,literal_row H p₁ _ h₁]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin,h0,h1]

/-- Mapping a finite actual label to its natural-number code changes no row value. -/
theorem mapped_weight (cs : List (Fin s×List ℕ)) (x : ℕ → Bool) :
    W.weight H (cs.map D.factor) x=
      (cs.map (fun row => H row.1 (fun j => x (row.2.getD j.val 0)))).prod := by
  simp only [W.weight,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro row _
  simp only [D.factor,W.rowValue,dite_eq_left row.1.isLt]

/-- Flat heterogeneous scopes reproduce the product of literal factor records.
Only each target row's arity is used; no incidence or support property appears. -/
theorem weight_data (cs : List (Fin s×List ℕ))
    (hc : ∀row∈cs,row.2.length=(D.family s b row.1).count) (x : ℕ → Bool) :
    F.weight (s:=s) (arity:=fun k=>b k*2) (D.family s b) H (cs.map Prod.fst)
      (fun k => x ((cs.flatMap Prod.snd).getD k 0))=
      W.weight H (cs.map D.factor) x := by
  rw [mapped_weight]
  induction cs with
  | nil => simp
  | cons row cs ih =>
      rcases row with ⟨i,scope⟩
      have hp : scope.length=(D.family s b i).count := hc (i,scope) (by simp)
      have hs : ∀row∈cs,row.2.length=(D.family s b row.1).count :=
        fun row hr => hc row (by simp [hr])
      simp only [List.map_cons,List.flatMap_cons,List.prod_cons,F.weight_cons]
      apply congrArg₂ (· * ·)
      · congr 1
        funext j
        rw [List.getD_append _ _ _ _ (by omega)]
      · have he : (fun k => x ((scope++cs.flatMap Prod.snd).getD ((D.family s b i).count+k) 0))=
            (fun k => x ((cs.flatMap Prod.snd).getD k 0)) := by
          funext k
          rw [←hp,List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
        rw [he]
        exact ih hs

include h₀ h₁ in
theorem raw_weight (r : C.Raw u) (x : ℕ → Bool) :
    W.weight H (D.raw (u:=u) (s:=s) (a:=a) (b:=b) recipe p₀ p₁ r).factors x=
      if x 0=false ∧ x 1=true then
        Pn.weight (s:=s) (arity:=fun k=>b k*2) (D.family s b) H (B.query (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (D.family u a) (D.family s b) recipe r) x
      else 0 := by
  rw [D.raw,weight_append,guards_weight H p₀ p₁ h₀ h₁]
  by_cases h : x 0=false ∧ x 1=true
  · simp only [ite_eq_left h,mul_one]
    exact (weight_data H (B.data (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (D.family u a) (D.family s b) recipe r)
      (B.data_length (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (D.family u a) (D.family s b) recipe r) x).symm
  · simp only [ite_eq_right h,mul_zero]

/-- The ordinary total reader agrees with the pinned-source reader on every
natural address, including out-of-range defaults. -/
theorem extend_anchor {v : ℕ} (q r : Bool) (x : Fin v → Bool) :
    W.extend (Fin.cons q (Fin.cons r x))=Pn.anchor q r x :=
  Pn.read_anchor q r x

include h₀ h₁ in
/-- The two reserved constants have exactly one supported assignment. All
original declared variables retain their full independent Boolean sum. -/
theorem value_fixed (r : C.Raw u) :
    W.value H (D.raw (u:=u) (s:=s) (a:=a) (b:=b) recipe p₀ p₁ r)=
      Pn.fixed (s:=s) (arity:=fun k=>b k*2) (D.family s b) H (B.query (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (D.family u a) (D.family s b) recipe r) false true := by
  unfold W.value
  change (∑x : Fin (r.variables+2) → Bool,
    W.weight H (D.raw (u:=u) (s:=s) (a:=a) (b:=b) recipe p₀ p₁ r).factors (W.extend x))=_
  rw [Pn.sum_cons]
  simp_rw [Pn.sum_cons,raw_weight H recipe p₀ p₁ h₀ h₁,extend_anchor]
  simp [Pn.fixed,Pn.anchor]
  rfl

include h₀ h₁ in
/-- Exact raw semantics, even before source validation. Each finite literal
recipe is evaluated over the same original assignment and target field. -/
theorem value_raw (r : C.Raw u) :
    W.value H (D.raw (u:=u) (s:=s) (a:=a) (b:=b) recipe p₀ p₁ r)=
      C.value (s:=u) (arity:=fun k=>a k*2) (D.family u a) (D.coefficient (u:=u) (s:=s) (a:=a) (b:=b) H recipe) r := by
  rw [value_fixed H recipe p₀ p₁ h₀ h₁]
  exact B.query_value (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2) (D.family u a) (D.family s b) recipe H r

include h₀ h₁ in
/-- Validated-input interface consumed by the actual mixed-block compiler. -/
theorem value (r : D.Input (u:=u) (a:=a)) :
    W.value H (D.raw (u:=u) (s:=s) (a:=a) (b:=b) recipe p₀ p₁ r.val)=
      C.value (s:=u) (arity:=fun k=>a k*2) (D.family u a) (D.coefficient (u:=u) (s:=s) (a:=a) (b:=b) H recipe) r.val :=
  value_raw H recipe p₀ p₁ h₀ h₁ r.val

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockSemantics
end
