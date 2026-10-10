import Holant.Proofs.Hardness.SparseUnitLocal
import Holant.ChargeConservation
import Holant.Complexity.EncodedHolantOutputSize
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Prefix

/-! The literal native ONE/TWO problem over any original fixed coefficient
field. Imbalance is a proved zero-value case, including each individual full
edge-end summand. No matching existence or nonzero partition is assumed. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.SparseUnitValue
open Holant Holant.Complexity FixedGadgetSubstitution
open SparseUnitLocal
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {K : Type*} [Field K]

def arity (_ : ℕ) : ℕ := 3
def palette (i : Fin 2) : Signature K (arity i.val) := if i.val=0 then ONE else TWO
abbrev Input := ExactSignatureTables.Input 2 1 arity
abbrev encoding := RawClosedNetwork.validatedEncoding 2 1 arity

def network (r : Input) : Network K 0 := r.val.realize r.property palette (fun _=>Signature.disequality)
def value (r : Input) : K := (network r).denote Fin.elim0
abbrev Ends (r : Input) := (Fin r.val.edges.length × Bool) → Bool

def count0 (r : Input) : ℕ := occurrences 0 r.val
def count1 (r : Input) : ℕ := occurrences 1 r.val

theorem one_weight (x : Fin 3 → Bool) (h : (ONE x : K)≠0) : weight x=1 := by
  have hw : weight x=(if x 0 then 1 else 0)+(if x 1 then 1 else 0)+(if x 2 then 1 else 0) :=
    Fin.sum_univ_three _
  rw [hw]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2
  all_goals try norm_num [ONE,h0,h1,h2] at h
  all_goals norm_num [h0,h1,h2]

theorem two_weight (x : Fin 3 → Bool) (h : (TWO x : K)≠0) : weight x=2 := by
  have hw := one_weight (K:=K) (fun i=>!x i) h
  have hc := weight_compl_add x
  omega

def labelScore (i : ℕ) : ℤ := if i=0 then -1 else 1

theorem score_sum (r : Input) :
    (∑v : Fin r.val.vertices.length,labelScore (r.val.signatureLabel r.property v).val)=
      (count1 r : ℤ)-(count0 r : ℤ) := by
  have hfun (v : Fin r.val.vertices.length) :
      labelScore (r.val.signatureLabel r.property v).val=
        (if (r.val.vertices.get v).1=1 then (1 : ℤ) else 0)-
        (if (r.val.vertices.get v).1=0 then (1 : ℤ) else 0) := by
    have hv := (r.property.1 v).1
    change labelScore (r.val.vertices.get v).1=_
    have hc : (r.val.vertices.get v).1=0 ∨ (r.val.vertices.get v).1=1 := by omega
    rcases hc with h|h
    all_goals simp only [List.get_eq_getElem] at h
    all_goals simp [labelScore,h]
  simp_rw [hfun]
  rw [Finset.sum_sub_distrib]
  have hc (label : ℕ) : (∑v : Fin r.val.vertices.length,
      if (r.val.vertices.get v).1=label then (1 : ℤ) else 0)=(occurrences label r.val : ℤ) := by
    have hn := Compiler.indicator_sum label r.val.vertices
    have hf := List.ofFn_getElem_eq_map r.val.vertices
      (fun row : RawVertex=>if row.1=label then (1 : ℕ) else 0)
    rw [←hf,List.sum_ofFn] at hn
    exact_mod_cast hn
  rw [hc,hc]
  rfl

theorem assignment_balanced (r : Input) (z : Ends r)
    (hz : (network (K:=K) r).assignmentTerm Fin.elim0 z≠0) : count0 r=count1 r := by
  have total := (network (K:=K) r).sum_charge_eq_zero_of_native_term (fun _=>rfl) Fin.elim0 z hz
  have hlocal (v : Fin r.val.vertices.length) :
      charge ((network (K:=K) r).shape.assignment Fin.elim0 z v)=
        labelScore (r.val.signatureLabel r.property v).val := by
    have hn := (network (K:=K) r).vertex_ne_zero_of_assignmentTerm_ne_zero Fin.elim0 z hz v
    change (if (r.val.signatureLabel r.property v).val=0 then (ONE : Signature K 3) else TWO)
      ((network (K:=K) r).shape.assignment Fin.elim0 z v)≠0 at hn
    by_cases hl : (r.val.signatureLabel r.property v).val=0
    · rw [if_pos hl] at hn
      rw [charge,one_weight _ hn]
      simp [labelScore,hl,network,RawClosedNetwork.realize,RawClosedNetwork.shape,arity]
    · rw [if_neg hl] at hn
      rw [charge,two_weight _ hn]
      simp [labelScore,hl,network,RawClosedNetwork.realize,RawClosedNetwork.shape,arity]
  change (∑v : Fin r.val.vertices.length,charge ((network (K:=K) r).shape.assignment Fin.elim0 z v))=0 at total
  simp_rw [hlocal] at total
  rw [score_sum] at total
  exact_mod_cast (sub_eq_zero.mp total).symm

theorem zero_of_unbalanced (r : Input) (h : count0 r≠count1 r) : (value r : K)=0 := by
  change (∑z : Ends r,(network (K:=K) r).assignmentTerm Fin.elim0 z)=0
  apply Finset.sum_eq_zero
  intro z _
  by_contra hz
  exact h (assignment_balanced r z hz)

end
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.SparseUnitValue
