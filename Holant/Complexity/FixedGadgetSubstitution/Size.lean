import Holant.Complexity.FixedGadgetSubstitution.WellFormed
import Holant.Complexity.OutputSize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Bit-size bounds for the literal replacement codec, including every original
and generated label, vertex record, boundary incidence, and internal edge ID. -/
namespace Holant.Complexity.FixedGadgetSubstitution
open Computability RawClosedNetwork

 theorem nat_code_length_le (n : ℕ) : (encodingNatBool.encode n).length ≤ n := by
  change (encodeNat n).length ≤ n
  rw [Holant.Algebraic.encodeNat_length]
  exact Nat.size_le.mpr n.lt_two_pow_self

 theorem framedList_length_le {α : Type} (e : Encoding α Bool) (xs : List α) (C : ℕ)
    (h : ∀ x ∈ xs, (e.encode x).length ≤ C) :
    (framedListEncode e xs).length ≤ (2*C+2)*xs.length+1 := by
  induction xs with
  | nil => simp [framedListEncode]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [framedListEncode, List.length_cons, List.length_append,
      Holant.Algebraic.frame_length]
    nlinarith

 theorem endpoint_length_le (p : RawEndpoint) (E : ℕ) (hp : p.1 ≤ E) :
    (endpointEncoding.encode p).length ≤ 2*E+2 := by
  have hn := nat_code_length_le p.1
  rw [endpointEncoding, framedProductEncoding_length]
  have hb : (encodingBoolBool.encode p.2).length = 1 := by cases p.2 <;> rfl
  rw [hb]
  omega

 theorem raw_length_le (r : RawClosedNetwork) {s b : ℕ} {arity : ℕ → ℕ}
    (hr : r.WellFormed s b arity) (A : ℕ) (ha : ∀ label < s, arity label ≤ A) :
    (encoding.encode r).length ≤
      2*((2*(2*s+2+(4*r.edges.length+6)*A)+2)*r.vertices.length+1)+1+
        ((2*b+2)*r.edges.length+1) := by
  have hv : ∀ row ∈ r.vertices, (vertexEncoding.encode row).length ≤
      2*s+2+(4*r.edges.length+6)*A := by
    intro row hrow
    obtain ⟨v, rfl⟩ := List.mem_iff_get.mp hrow
    have hl := hr.1 v
    have hport : ∀ p ∈ (r.vertices.get v).2,
        (endpointEncoding.encode p).length ≤ 2*r.edges.length+2 := by
      intro p hp
      apply endpoint_length_le
      apply Nat.le_of_lt
      apply (r.mem_expectedEndpoints_iff p).mp
      apply hr.2.2.mem_iff.mp
      exact List.mem_flatten.mpr ⟨(r.vertices.get v).2,
        List.mem_map.mpr ⟨r.vertices.get v,List.get_mem _ v,rfl⟩, hp⟩
    have hlist := framedList_length_le endpointEncoding (r.vertices.get v).2 _ hport
    have hn := (nat_code_length_le (r.vertices.get v).1).trans (Nat.le_of_lt hl.1)
    have hlen := ha _ hl.1
    rw [←hl.2] at hlen
    rw [vertexEncoding,framedProductEncoding_length]
    change 2*(encodingNatBool.encode (r.vertices.get v).1).length+1+
      (framedListEncode endpointEncoding (r.vertices.get v).2).length ≤ _
    nlinarith
  have he : ∀ label ∈ r.edges, (encodingNatBool.encode label).length ≤ b := by
    intro label hl
    obtain ⟨e, rfl⟩ := List.mem_iff_get.mp hl
    exact (nat_code_length_le _).trans (Nat.le_of_lt (hr.2.1 e))
  have hvertices := framedList_length_le vertexEncoding r.vertices _ hv
  have hedges := framedList_length_le encodingNatBool r.edges _ he
  change ((framedProductEncoding (framedListEncoding vertexEncoding)
    (framedListEncoding encodingNatBool)).encode (r.vertices,r.edges)).length ≤ _
  rw [framedProductEncoding_length]
  change 2*(framedListEncode vertexEncoding r.vertices).length+1+
    (framedListEncode encodingNatBool r.edges).length ≤ _
  omega

 theorem sum_map_le {α : Type} (f : α → ℕ) (xs : List α) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ C*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [Nat.mul_add, Nat.mul_one]
    omega

 theorem replace_counts_le (templates : ℕ → Template) (r : RawClosedNetwork)
    {sourceCount b : ℕ} {sourceArity : ℕ → ℕ}
    (hr : r.WellFormed sourceCount b sourceArity) (V E : ℕ)
    (hb : ∀ label < sourceCount, (templates label).vertices.length ≤ V ∧
      (templates label).edges.length ≤ E) :
    (replace templates r).vertices.length ≤ V*(encoding.encode r).length ∧
    (replace templates r).edges.length ≤ (E+1)*(encoding.encode r).length := by
  have hv : ∀ row ∈ r.vertices, (templates row.1).vertices.length ≤ V ∧
      (templates row.1).edges.length ≤ E := by
    intro row hrow
    obtain ⟨v,rfl⟩ := List.mem_iff_get.mp hrow
    exact hb _ (hr.1 v).1
  have hc := r.counts_le_encoded_length
  have h₁ := sum_map_le (fun row : RawVertex => (templates row.1).vertices.length)
    r.vertices V (fun row hrow => (hv row hrow).1)
  have h₂ := sum_map_le (fun row : RawVertex => (templates row.1).edges.length)
    r.vertices E (fun row hrow => (hv row hrow).2)
  rw [replace_vertex_count,replace_edge_count]
  constructor <;> nlinarith

/-- A concrete polynomial in the original physical input bit length. -/
noncomputable def querySizePolynomial (s b A V E : ℕ) : Polynomial ℕ :=
  2*((2*(2*Polynomial.C s+2+(4*(Polynomial.C E+1)*Polynomial.X+6)*Polynomial.C A)+2)*
    (Polynomial.C V*Polynomial.X)+1)+1+
      ((2*Polynomial.C b+2)*((Polynomial.C E+1)*Polynomial.X)+1)

 theorem replace_length_le (templates : ℕ → Template) (r : RawClosedNetwork)
    {sourceCount s b : ℕ} {sourceArity arity : ℕ → ℕ}
    (hr : r.WellFormed sourceCount b sourceArity)
    (hg : ∀ label < sourceCount, (templates label).WellFormed s b arity ∧
      (templates label).boundary = sourceArity label)
    (A V E : ℕ) (ha : ∀ label < s, arity label ≤ A)
    (hb : ∀ label < sourceCount, (templates label).vertices.length ≤ V ∧
      (templates label).edges.length ≤ E) :
    (encoding.encode (replace templates r)).length ≤
      (querySizePolynomial s b A V E).eval (encoding.encode r).length := by
  have hh := raw_length_le (replace templates r) (replace_wellFormed templates r hr hg) A ha
  have hc := replace_counts_le templates r hr V E hb
  apply hh.trans
  simp only [querySizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  have hm := Nat.mul_le_mul_left 4 hc.2
  have ha' := Nat.mul_le_mul_right A (Nat.add_le_add_right hm 6)
  have hs := Nat.add_le_add_left ha' (2*s+2)
  have hs' := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hs) 2
  have ht := Nat.mul_le_mul hs' hc.1
  have he := Nat.mul_le_mul_left (2*b+2) hc.2
  simp only [Nat.mul_assoc] at hm ha' hs hs' ht he ⊢
  omega

end Holant.Complexity.FixedGadgetSubstitution
