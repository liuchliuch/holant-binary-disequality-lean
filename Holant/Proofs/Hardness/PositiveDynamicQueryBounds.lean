import Holant.Proofs.Hardness.PositiveDynamicQueries
import Holant.Proofs.Hardness.PositiveDynamicPolynomialBounds
import Holant.Complexity.FixedGadgetSubstitution.Size

/-! Concrete sizes of the actual original-q graph writer, in original physical
input bytes. Counts retain unmarked rows separately from the inlined blocks. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryBounds
open Holant Holant.Complexity Computability FixedGadgetSubstitution RawClosedNetwork
namespace Q
export PositiveDynamicQueries (count templates raw stageValue value queries sampleCount)
export ExactTwoChainQueries (arity Input TargetInput sourceEncoding targetEncoding)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

def retained (r : Q.Input) : ℕ := (r.val.vertices.filter (fun row=>row.1!=1)).length

theorem retained_le (r : Q.Input) : retained r≤r.val.vertices.length := List.length_filter_le _ _

theorem sum_marked (rs : List RawVertex) (u v : ℕ) :
    (rs.map (fun row=>if row.1=1 then u else v)).sum=
      (rs.filter (fun row=>row.1==1)).length*u+
      (rs.filter (fun row=>row.1!=1)).length*v := by
  induction rs with
  | nil => simp
  | cons row rs ih =>
    by_cases h : row.1=1 <;> simp [h,ih,Nat.add_mul] <;> omega

theorem raw_vertices (n k : ℕ) (hn : 0<n) (r : Q.Input) :
    (Q.raw n k r).vertices.length=retained r+Q.count r*(n*(k+1)) := by
  rw [Q.raw,replace_vertex_count]
  have ht : ∀i, (Q.templates n k i).vertices.length=if i=1 then n*(k+1) else 1 := by
    intro i
    by_cases h : i=1
    · simp only [Q.templates,h,ite_true]
      exact (PositiveDynamicStageSeriesRecords.counts 0 0 n k hn).1
    · simp [Q.templates,h,identityTemplate]
  simp_rw [ht]
  rw [sum_marked]
  simp only [Nat.mul_one,retained,Q.count,FixedGadgetSubstitution.occurrences,Nat.add_comm]

theorem raw_edges (n k : ℕ) (hn : 0<n) (r : Q.Input) :
    (Q.raw n k r).edges.length=r.val.edges.length+Q.count r*(2*n*(k+1)-2) := by
  rw [Q.raw,replace_edge_count]
  have ht : ∀i, (Q.templates n k i).edges.length=if i=1 then 2*n*(k+1)-2 else 0 := by
    intro i
    by_cases h : i=1
    · simp only [Q.templates,h,ite_true]
      exact (PositiveDynamicStageSeriesRecords.counts 0 0 n k hn).2
    · simp [Q.templates,h,identityTemplate]
  simp_rw [ht]
  rw [sum_marked]
  simp only [Nat.mul_zero,Nat.add_zero,Q.count,FixedGadgetSubstitution.occurrences]

variable (d : PositiveDynamicParameters.Data)

theorem value_vertices (r : Q.Input) (k : ℕ) :
    (Q.value d (k,r)).val.vertices.length=
      retained r+Q.count r*(d.length (Q.count r)*(k+1)) :=
  raw_vertices _ _ (d.length_pos _) r

theorem value_edges (r : Q.Input) (k : ℕ) :
    (Q.value d (k,r)).val.edges.length=
      r.val.edges.length+Q.count r*(2*d.length (Q.count r)*(k+1)-2) :=
  raw_edges _ _ (d.length_pos _) r

def sizeEnvelope (d : PositiveDynamicParameters.Data) (L : ℕ) : ℕ :=
  L+4*d.constant*(L+1)^4

/-- Both literal vertex and edge counts are bounded by a fixed polynomial of
the original graph's encoding length; the multiplier is fixed signature data. -/
theorem value_counts_le (r : Q.Input) (k : ℕ) (hk : k≤(Q.count r+1)^2) :
    (Q.value d (k,r)).val.vertices.length≤sizeEnvelope d (Q.sourceEncoding.encode r).length ∧
    (Q.value d (k,r)).val.edges.length≤sizeEnvelope d (Q.sourceEncoding.encode r).length := by
  let L := (Q.sourceEncoding.encode r).length
  have hm : Q.count r≤L := occurrences_le_input_length 1 r.val
  have hc := r.val.counts_le_encoded_length
  change r.val.vertices.length+r.val.edges.length≤L at hc
  have hcv : r.val.vertices.length≤L := by omega
  have hce : r.val.edges.length≤L := by omega
  have hr := (retained_le r).trans hcv
  have hb := PositiveDynamicPolynomialBounds.replaced_size_le d (Q.count r) k hk
  have hp : (Q.count r+1)^4≤(L+1)^4 := Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 4
  have hbp : Q.count r*(d.length (Q.count r)*(k+1))≤2*d.constant*(L+1)^4 :=
    hb.trans (Nat.mul_le_mul_left _ hp)
  have he : Q.count r*(2*d.length (Q.count r)*(k+1)-2)≤
      2*(Q.count r*(d.length (Q.count r)*(k+1))) := by
    calc
      _ ≤ Q.count r*(2*d.length (Q.count r)*(k+1)) :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = _ := by ring
  rw [value_vertices,value_edges]
  change _≤L+4*d.constant*(L+1)^4 ∧ _≤L+4*d.constant*(L+1)^4
  constructor <;> nlinarith

/-- A concrete polynomial bound for one faithfully encoded oracle query. -/
noncomputable def querySizePolynomial (d : PositiveDynamicParameters.Data) : Polynomial ℕ :=
  let S := Polynomial.X+4*Polynomial.C d.constant*(Polynomial.X+1)^4
  2*((2*(4+(4*S+6)*4)+2)*S+1)+1+(4*S+1)

theorem value_length_le (r : Q.Input) (k : ℕ) (hk : k≤(Q.count r+1)^2) :
    (Q.targetEncoding.encode (Q.value d (k,r))).length≤
      (querySizePolynomial d).eval (Q.sourceEncoding.encode r).length := by
  have hs := value_counts_le d r k hk
  have h := raw_length_le (Q.value d (k,r)).val (Q.value d (k,r)).property 4
    (by intros; exact Nat.le_refl 4)
  change (Q.targetEncoding.encode (Q.value d (k,r))).length≤_ at h
  apply h.trans
  simp only [querySizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,
    Polynomial.eval_pow]
  change _≤2*((2*(4+(4*sizeEnvelope d (Q.sourceEncoding.encode r).length+6)*4)+2)*
    sizeEnvelope d (Q.sourceEncoding.encode r).length+1)+1+
    (4*sizeEnvelope d (Q.sourceEncoding.encode r).length+1)
  have hm := Nat.mul_le_mul_left 4 hs.2
  have ha := Nat.mul_le_mul_right 4 (Nat.add_le_add_right hm 6)
  have hb := Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_left ha 4)) 2
  have hv := Nat.mul_le_mul hb hs.1
  have he := Nat.mul_le_mul_left 4 hs.2
  norm_num at h ⊢
  omega

theorem query_length_le (r : Q.Input) (q : Q.TargetInput) (hq : q∈Q.queries d r) :
    (Q.targetEncoding.encode q).length≤
      (querySizePolynomial d).eval (Q.sourceEncoding.encode r).length := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  have hk' : k≤(Q.count r+1)^2 := by
    have hk'' := List.mem_range.mp hk
    have hc := ThreeModeAnnihilator.rootIndices_length_le (Q.count r)
    change k<(ThreeModeAnnihilator.rootIndices (Q.count r)).length+1 at hk''
    omega
  exact value_length_le d r k hk'


theorem query_count_input_le (r : Q.Input) :
    (Q.queries d r).length≤((Q.sourceEncoding.encode r).length+1)^2+1 := by
  have hm : Q.count r≤(Q.sourceEncoding.encode r).length :=
    occurrences_le_input_length 1 r.val
  exact (PositiveDynamicQueries.query_count_le d r).trans
    (Nat.add_le_add_right (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 2) 1)

/-- The complete query tape, including all frames and terminators. -/
def batchSizePolynomial : Polynomial ℕ :=
  (2*querySizePolynomial d+2)*((Polynomial.X+1)^2+1)+1

theorem queries_length_le (r : Q.Input) :
    ((framedListEncoding Q.targetEncoding).encode (Q.queries d r)).length≤
      (batchSizePolynomial d).eval (Q.sourceEncoding.encode r).length := by
  have h := framedList_length_le Q.targetEncoding (Q.queries d r)
    ((querySizePolynomial d).eval (Q.sourceEncoding.encode r).length)
    (fun q hq=>query_length_le d r q hq)
  change (framedListEncode Q.targetEncoding (Q.queries d r)).length≤_
  apply h.trans
  have hc := query_count_input_le d r
  simpa only [batchSizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_pow]
    using Nat.add_le_add_right (Nat.mul_le_mul_left
      (2*(querySizePolynomial d).eval (Q.sourceEncoding.encode r).length+2) hc) 1

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicQueryBounds
