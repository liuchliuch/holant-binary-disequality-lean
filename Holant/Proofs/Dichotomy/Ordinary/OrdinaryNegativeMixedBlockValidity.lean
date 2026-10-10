import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockData
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativePhaseBundleValidity

/-! Actual mixed-block occurrence validation. The hypothesis concerns only
the finite literal recipes. Every input instance, repeated variable address,
private address and constant pin is checked by the emitted count equations. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockValidity
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
namespace B
export GeneralEOPairedFamilyBundleRaw (data row rowFor factor)
export GeneralEOPairedFamilyBundleValue (data_length query_valid)
end B
namespace M
export GeneralEOPairedFamilyMinorRaw (port)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem count_map {A : Type*} [Fintype A] [BEq A] [LawfulBEq A] [DecidableEq A] (xs : List A)
    (f : A→ℕ) (k : ℕ) : (xs.map f).count k=∑a : A,xs.count a*(if f a=k then 1 else 0) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons,List.count_cons,ih,add_mul,Finset.sum_add_distrib]
      congr 1
      simp only [beq_iff_eq,ite_mul,one_mul,zero_mul]
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy
        simp [Ne.symm hy]
      · simp

theorem even_map {A : Type*} [Fintype A] [BEq A] [LawfulBEq A] [DecidableEq A] (xs : List A)
    (h : ∀a,Even (xs.count a)) (f : A→ℕ) (k : ℕ) : Even ((xs.map f).count k) := by
  rw [count_map]
  have hs (S : Finset A) : Even (∑a∈S,xs.count a*(if f a=k then 1 else 0)) := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
        rw [Finset.sum_insert ha]
        apply Even.add _ ih
        split_ifs
        · simpa using h a
        · simp
  exact hs Finset.univ

variable {u s : ℕ} {a b : ℕ→ℕ}
variable (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b))
variable (p₀ p₁ : Fin s) (h₀ : b p₀.val=1) (h₁ : b p₁.val=1)

theorem row_addresses (r : GeneralEOPairedCSPFamilyRaw.Raw u) (v : ℕ) (i : Fin u) :
    (B.rowFor (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2)
      (family u a) (family s b) recipe r v i).flatMap Prod.snd=
        (ports recipe i).map (M.port (s:=u) (a:=fun k=>a k*2) (family u a) r v) := by
  simp only [B.rowFor,B.factor,ports,List.flatMap_map,Function.comp_def,List.map_flatMap,List.map_ofFn]

include h₀ h₁ in
theorem good (r : OrdinaryNegativeMixedBlockData.Input (u:=u) (a:=a)) :
    ∀row∈(raw recipe p₀ p₁ r.val).factors,
      row.1<s ∧ row.2.length=b row.1 ∧ ∀k∈row.2,k<r.val.variables+2 := by
  intro row hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨node,hn,rfl⟩ := List.mem_map.mp hr
    refine ⟨node.1.isLt,?_,?_⟩
    · exact B.data_length (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2)
        (family u a) (family s b) recipe r.val node hn
    · intro k hk
      have hvalid := B.query_valid (s:=u) (t:=s) (a:=fun k=>a k*2) (b:=fun k=>b k*2)
        (family u a) (family s b) recipe r.val r.property
      exact hvalid.2 k (List.mem_flatMap.mpr ⟨node,hn,hk⟩)
  · exact OrdinaryNegativePhaseBundleValidity.guards_good p₀ p₁ h₀ h₁ r.val.variables row hr

variable (heven : EvenRecipe recipe)

include heven in
theorem row_even (r : GeneralEOPairedCSPFamilyRaw.Raw u) (v : ℕ) (i : Fin u) (k : ℕ) :
    Even ((B.rowFor (s:=u) (t:=s) (a:=fun j=>a j*2) (b:=fun j=>b j*2)
      (family u a) (family s b) recipe r v i).flatMap Prod.snd |>.count k) := by
  rw [row_addresses]
  exact even_map (ports recipe i) (heven i) _ k

include heven in
theorem raw_even (r : GeneralEOPairedCSPFamilyRaw.Raw u) (k : ℕ) :
    Even ((raw recipe p₀ p₁ r).degree k) := by
  rw [StableHigherCurrentOrdinarySquare.degree_flat]
  simp only [raw,List.flatMap_append,List.count_append]
  apply Even.add _ (OrdinaryNegativePhaseBundleValidity.guards_even p₀ p₁ k)
  simp only [List.flatMap_map,factor]
  change Even (((List.finRange r.labels.length).flatMap
    (B.row (s:=u) (t:=s) (a:=fun j=>a j*2) (b:=fun j=>b j*2)
      (family u a) (family s b) recipe r)).flatMap Prod.snd |>.count k)
  have hh (vs : List (Fin r.labels.length)) :
      Even ((vs.flatMap (B.row (s:=u) (t:=s) (a:=fun j=>a j*2) (b:=fun j=>b j*2)
        (family u a) (family s b) recipe r)).flatMap Prod.snd |>.count k) := by
    induction vs with
    | nil => simp
    | cons v vs ih =>
        simp only [List.flatMap_cons,List.flatMap_append,List.count_append]
        exact (row_even recipe heven r v.val (r.labels.get v) k).add ih
  exact hh _

include h₀ h₁ heven in
theorem valid (r : OrdinaryNegativeMixedBlockData.Input (u:=u) (a:=a)) :
    (raw recipe p₀ p₁ r.val).Valid s b := by
  have hg := good recipe p₀ p₁ h₀ h₁ r
  refine ⟨?_,?_,fun k _=>raw_even recipe p₀ p₁ heven r.val k⟩
  · intro v
    exact ⟨(hg _ (List.get_mem _ v)).1,(hg _ (List.get_mem _ v)).2.1⟩
  · intro p
    exact (hg _ (List.get_mem _ p.1)).2.2 _ (List.get_mem _ p.2)

def query (r : OrdinaryNegativeMixedBlockData.Input (u:=u) (a:=a)) : Raw.Input s b :=
  ⟨raw recipe p₀ p₁ r.val,valid recipe p₀ p₁ h₀ h₁ heven r⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockValidity
end
