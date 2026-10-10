import Holant.Proofs.Hardness.EOBinaryPlaneConjugateQueries
import Holant.Proofs.Hardness.EOBinaryPlaneGramAccess

/-! Common-extension conjugate interpolation on arbitrary validated two-label
native-X records. Zero lift entries and absent marked occurrences are included.
Positive moments keep the exact same incidence record and replace only the
second binary table by a positive Hadamard power of the original table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneConjugateNetwork
open Holant Holant.Complexity
open scoped BigOperators
namespace B
export EOBinaryPlaneCore (lift)
end B
namespace I
export EOBinaryPlaneConjugate (Grid monomial spectrum polynomial eval_spectrum filtered filtered_eval)
end I
namespace Q
export EOBinaryPlaneConjugateQueries (coefficients label coefficient_label)
end Q
set_option backward.isDefEq.respectTransparency false

variable {K L : Type*} [Field K] [Field L] [StarRing L]

omit [StarRing L] in
theorem masked_spectrum (into : K→+*L) (c : Fin 4→K) {n : ℕ}
    (selected : Fin n→Prop) [DecidablePred selected] (labels : Fin n→Fin 4) :
    into (∏v,if selected v then c (labels v) else 1)∈I.spectrum into c n := by
  classical
  let rows := Finset.univ.filter selected
  let powers : I.Grid n := fun j=>⟨(rows.filter fun v=>labels v=j).card,by
    have h := Finset.card_le_card (Finset.filter_subset (fun v=>labels v=j) rows)
    have h' := Finset.card_le_card (Finset.filter_subset selected Finset.univ)
    simp only [Finset.card_univ,Fintype.card_fin] at h'
    change rows.card≤n at h'
    change (Finset.filter _ rows).card<n+1
    omega⟩
  have hp : (∏v,if selected v then c (labels v) else 1)=I.monomial c powers := by
    rw [←Finset.prod_filter]
    change (∏v ∈ rows,c (labels v))=_
    rw [←Finset.prod_fiberwise' rows labels c]
    simp only [Finset.prod_const,I.monomial,powers]
  rw [hp]
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨powers,Finset.mem_univ _,rfl⟩

omit [StarRing L] in
theorem lift_spectrum (into : K→+*L) (f : Signature K 2) {n : ℕ}
    (selected : Fin n→Prop) [DecidablePred selected] (rows : Fin n→Fin 4→Bool) :
    into (∏v,if selected v then B.lift f (rows v) else 1)∈I.spectrum into (Q.coefficients f) n := by
  classical
  by_cases hs : ∀v,selected v → rows v 1= !(rows v 0) ∧ rows v 3= !(rows v 2)
  · have he : (∏v,if selected v then B.lift f (rows v) else 1)=
        ∏v,if selected v then Q.coefficients f (Q.label ![rows v 0,rows v 2]) else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases h : selected v
      · rw [ite_eq_left h,ite_eq_left h,Q.coefficient_label]
        simp only [B.lift,ite_eq_left (hs v h)]
      · rw [ite_eq_right h,ite_eq_right h]
    rw [he]
    exact masked_spectrum into (Q.coefficients f) selected _
  · obtain ⟨v,hv,hn⟩ : ∃v,∃ _ : selected v, ¬(rows v 1= !(rows v 0) ∧ rows v 3= !(rows v 2)) := by
      simpa only [not_forall] using hs
    have hz : (∏v,if selected v then B.lift f (rows v) else 1)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp only [ite_eq_left hv,B.lift,ite_eq_right hn]
    simp only [hz,map_zero]
    exact Finset.mem_insert_self _ _

def marked {n : ℕ} (f : Signature K 2) (selected : Fin n→Prop)
    [DecidablePred selected] (rows : Fin n→Fin 4→Bool) : K :=
  ∏v,if selected v then B.lift f (rows v) else 1

theorem marked_moments {A : Type*} [Fintype A] (into : K→+*L) (f : Signature K 2)
    {n : ℕ} (selected : Fin n→Prop) [DecidablePred selected]
    (base : A→K) (rows : A→Fin n→Fin 4→Bool) :
    (∑x,into (base x)*star (into (marked f selected (rows x))))=
      ∑k ∈ Finset.range (I.polynomial into (Q.coefficients f) n).natDegree,
        (I.polynomial into (Q.coefficients f) n).coeff (k+1)*
          into (∑x,base x*(marked f selected (rows x))^(k+1)) := by
  classical
  simp_rw [map_sum,map_mul,map_pow,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hspec : into (marked f selected (rows x))∈I.spectrum into (Q.coefficients f) n :=
    lift_spectrum into f selected (rows x)
  rw [←I.eval_spectrum into (Q.coefficients f) n _ hspec,←I.filtered_eval]
  unfold I.filtered
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Field L] [StarRing L] in
theorem lift_power (f : Signature K 2) (x : Fin 4→Bool) (k : ℕ) (hk : 0<k) :
    B.lift (fun z=>f z^k) x=(B.lift f x)^k := by
  unfold B.lift
  split_ifs <;> simp [Nat.ne_of_gt hk]

omit [StarRing L] in
theorem lift_map (into : K→+*L) (f : Signature K 2) (x : Fin 4→Bool) :
    B.lift (fun z=>into (f z)) x=into (B.lift f x) := by
  unfold B.lift
  split_ifs <;> simp

theorem lift_conjugate (into : K→+*L) (f : Signature K 2) (x : Fin 4→Bool) :
    B.lift (fun z=>star (into (f z))) x=star (into (B.lift f x)) := by
  unfold B.lift
  split_ifs <;> simp

abbrev Input := EOBinaryPlaneGramAccess.Input

def selected (r : Input) (v : Fin r.val.vertices.length) : Prop := r.val.signatureLabel r.property v≠0

instance selectedDecidable (r : Input) : DecidablePred (selected r) := fun v=>
  inferInstanceAs (Decidable (r.val.signatureLabel r.property v≠0))

def row (r : Input) (a : Fin r.val.edges.length→Bool) (v : Fin r.val.vertices.length) : Fin 4→Bool :=
  (r.val.shape r.property).assignment Fin.elim0 (fun e=>if e.2 then !(a e.1) else a e.1) v

def network {J : Type*} [Field J] (f g : Signature J 2) (r : Input) : Network J 0 :=
  r.val.realize r.property (EOBinaryPlaneGramGraph.palette f g) (fun _=>Signature.disequality)

def value {J : Type*} [Field J] (f g : Signature J 2) (r : Input) : J :=
  (network f g r).denote Fin.elim0

theorem native_value {J : Type*} [Field J] (f g : Signature J 2) (r : Input) :
    value f g r=∑a : Fin r.val.edges.length→Bool,∏v : Fin r.val.vertices.length,
      if selected r v then B.lift g (row r a v) else B.lift f (row r a v) := by
  rw [value,EOBinaryPlaneOpen.native_sum _ (fun _=>rfl)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  simp only [network,RawClosedNetwork.realize,EOBinaryPlaneGramGraph.palette,row,selected,ite_not,ite_apply]

private theorem split_product {J : Type*} [CommMonoid J] {n : ℕ}
    (selected : Fin n→Prop) [DecidablePred selected] (f g : Fin n→J) :
    (∏v,if selected v then g v else f v)=
      (∏v,if selected v then 1 else f v)*(∏v,if selected v then g v else 1) := by
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  by_cases h : selected v <;> simp [h]

def base (f : Signature K 2) (r : Input) (a : Fin r.val.edges.length→Bool) : K :=
  ∏v,if selected r v then 1 else B.lift f (row r a v)

theorem mixed_value (into : K→+*L) (f : Signature K 2) (r : Input) :
    value (fun z=>into (f z)) (fun z=>star (into (f z))) r=
      ∑a : Fin r.val.edges.length→Bool,into (base f r a)*
        star (into (marked f (selected r) (row r a))) := by
  rw [native_value]
  apply Finset.sum_congr rfl
  intro a _
  rw [split_product]
  simp only [base,marked,map_prod,star_prod,lift_map,lift_conjugate]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro v _ <;>
    by_cases h : selected r v <;> simp [h]

omit [Field L] [StarRing L] in
theorem power_value (f : Signature K 2) (r : Input) (k : ℕ) (hk : 0<k) :
    value f (fun z=>f z^k) r=
      ∑a : Fin r.val.edges.length→Bool,base f r a*(marked f (selected r) (row r a))^k := by
  rw [native_value]
  apply Finset.sum_congr rfl
  intro a _
  rw [split_product]
  simp only [base,marked,lift_power f _ k hk]
  congr 1
  rw [←Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro v _
  by_cases h : selected r v <;> simp [h]

/-- Conjugation is recovered only in the named extension L. All power queries
are values in the original K, on the same validated incidence record. -/
theorem network_moments (into : K→+*L) (f : Signature K 2) (r : Input) :
    value (fun z=>into (f z)) (fun z=>star (into (f z))) r=
      ∑k ∈ Finset.range (I.polynomial into (Q.coefficients f) r.val.vertices.length).natDegree,
        (I.polynomial into (Q.coefficients f) r.val.vertices.length).coeff (k+1)*
          into (value f (fun z=>f z^(k+1)) r) := by
  rw [mixed_value]
  have h := marked_moments into f (selected r) (base f r) (row r)
  simpa only [power_value f r _ (Nat.zero_lt_succ _)] using h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneConjugateNetwork
